//===----------------------------------------------------------------------===//
//
// This source file is part of the SwiftNIO open source project
//
// Copyright (c) 2017-2021 Apple Inc. and the SwiftNIO project authors
// Licensed under Apache License v2.0
//
// See LICENSE.txt for license information
// See CONTRIBUTORS.txt for the list of SwiftNIO project authors
//
// SPDX-License-Identifier: Apache-2.0
//
//===----------------------------------------------------------------------===//

@_implementationOnly import CNIOBoringSSL
import NIOCore

internal let SSL_MAX_RECORD_SIZE = 16 * 1024

/// This is used as the application data index to store pointers to `SSLConnection` objects in
/// `SSL` objects. It is only safe to use after BoringSSL initialization. As it's declared global,
/// it will be lazily initialized and protected by a dispatch_once, ensuring that it's thread-safe.
internal let sslConnectionExDataIndex = CNIOBoringSSL_SSL_get_ex_new_index(0, nil, nil, nil, nil)

/// Encodes the return value of a non-blocking BoringSSL method call.
///
/// This enum maps BoringSSL's return values to a small number of cases. A success
/// value naturally maps to `.complete`, and most errors map to `.failed`. However,
/// the BoringSSL "errors" `WANT_READ` and `WANT_WRITE` are mapped to `.incomplete`, to
/// help distinguish them from the other error cases. This makes it easier for code to
/// handle the "must wait for more data" case by calling it out directly.
enum AsyncOperationResult<T> {
    case incomplete
    case complete(T)
    case failed(BoringSSLError)
}

/// A wrapper class that encapsulates BoringSSL's `SSL *` object.
///
/// This class represents a single TLS connection, and performs all of crypto and record
/// framing required by TLS. It also records the configuration and parent `NIOSSLContext` object
/// used to create the connection.
internal final class SSLConnection {
    
    internal enum OperatingMode {
        case classic
        case quic
        
        var isQuic:Bool {
            self == .quic
        }
    }
    enum Errors:Error {
        case invalidQuicCryptoFrame
    }
    
    private let ssl: OpaquePointer
    internal let parentContext: NIOSSLContext
    private var bio: ByteBufferBIO?
    internal var expectedHostname: String?
    internal var role: ConnectionRole?
    internal var parentHandler: NIOSSLHandler?
    internal var eventLoop: EventLoop?

    /// Deprecated in favour of customVerificationManager
    private var verificationCallback: NIOSSLVerificationCallback?
    internal var customVerificationManager: CustomVerifyManager?
    internal var customPrivateKeyResult: Result<ByteBuffer, Error>?
    /// Boring SSL QUIC extension
    internal var epoch:ssl_encryption_level_t = ssl_encryption_initial
    internal private(set) var mode:OperatingMode
    
    private var quicMethods = SSL_QUIC_METHOD(
        set_read_secret: { SSLConnection.setReadSecret($0, $1, $2, $3, $4) },
        set_write_secret: { SSLConnection.setWriteSecret($0, $1, $2, $3, $4) },
        add_handshake_data: { SSLConnection.addHandshakeData($0, $1, $2, $3) },
        flush_flight: { SSLConnection.flushFlight($0) },
        send_alert: { SSLConnection.sendAlert($0, $1, $2) }
    )
    internal var outboundQueue:ByteBuffer = ByteBuffer()
    private var quicDelegate:(any NIOSSLQuicDelegate)? = nil
    private var hasProvidedPeersParams:Bool = false

    /// Whether certificate hostnames should be validated.
    var validateHostnames: Bool {
        if case .fullVerification = parentContext.configuration.certificateVerification {
            return true
        }
        return false
    }

    init(ownedSSL: OpaquePointer, parentContext: NIOSSLContext) {
        self.ssl = ownedSSL
        self.parentContext = parentContext
        self.mode = .classic
        // We pass the SSL object an unowned reference to this object.
        let pointerToSelf = Unmanaged.passUnretained(self).toOpaque()
        CNIOBoringSSL_SSL_set_ex_data(self.ssl, sslConnectionExDataIndex, pointerToSelf)

        self.setRenegotiationSupport(self.parentContext.configuration.renegotiationSupport)
    }

    deinit {
        CNIOBoringSSL_SSL_free(ssl)
    }

    /// Configures this as a server connection.
    func setAcceptState() {
        CNIOBoringSSL_SSL_set_accept_state(ssl)
        self.role = .server
    }

    /// Configures this as a client connection.
    func setConnectState() {
        CNIOBoringSSL_SSL_set_connect_state(ssl)
        self.role = .client
    }

    func setAllocator(_ allocator: ByteBufferAllocator, maximumPreservedOutboundBufferCapacity: Int) {
        self.bio = ByteBufferBIO(
            allocator: allocator,
            maximumPreservedOutboundBufferCapacity: maximumPreservedOutboundBufferCapacity
        )

        // This weird dance where we pass the *exact same* pointer in to both objects is because, weirdly,
        // the BoringSSL docs claim that only one reference count will be consumed here. We therefore need to
        // avoid calling BIO_up_ref too many times.
        let bioPtr = self.bio!.retainedBIO()
        CNIOBoringSSL_SSL_set_bio(self.ssl, bioPtr, bioPtr)
    }

    /// Sets the value of the SNI extension to send to the server.
    ///
    /// This method must only be called with a hostname, not an IP address. Sending
    /// an IP address in the SNI extension is invalid, and may result in handshake
    /// failure.
    func setServerName(name: String) throws {
        CNIOBoringSSL_ERR_clear_error()
        let rc = name.withCString {
            CNIOBoringSSL_SSL_set_tlsext_host_name(ssl, $0)
        }
        guard rc == 1 else {
            throw BoringSSLError.invalidSNIName(BoringSSLError.buildErrorStack())
        }
        self.expectedHostname = name
    }

    /// Sets the BoringSSL old-style verification callback.
    ///
    /// This is deprecated in favour of the new-style verification callback in SSLContext.
    func setVerificationCallback(_ callback: @escaping NIOSSLVerificationCallback) {
        // Store the verification callback. We need to do this to keep it alive throughout the connection.
        // We'll drop this when we're told that it's no longer needed to ensure we break the reference cycles
        // that this callback inevitably produces.
        self.verificationCallback = callback

        // We need to know what the current mode is.
        let currentMode = CNIOBoringSSL_SSL_get_verify_mode(self.ssl)
        CNIOBoringSSL_SSL_set_verify(self.ssl, currentMode) { preverify, storeContext in
            // To start out, let's grab the certificate we're operating on.
            guard let certPointer = CNIOBoringSSL_X509_STORE_CTX_get_current_cert(storeContext) else {
                preconditionFailure(
                    "Can only have verification function invoked with actual certificate: bad store \(String(describing: storeContext))"
                )
            }
            CNIOBoringSSL_X509_up_ref(certPointer)
            let cert = NIOSSLCertificate.fromUnsafePointer(takingOwnership: certPointer)

            // Next, prepare the verification result.
            let verificationResult = NIOSSLVerificationResult(fromBoringSSLPreverify: preverify)

            // Now, grab the SSLConnection object.
            guard
                let ssl = CNIOBoringSSL_X509_STORE_CTX_get_ex_data(
                    storeContext,
                    CNIOBoringSSL_SSL_get_ex_data_X509_STORE_CTX_idx()
                )
            else {
                preconditionFailure("Unable to obtain SSL * from X509_STORE_CTX * \(String(describing: storeContext))")
            }
            let connection = SSLConnection.loadConnectionFromSSL(OpaquePointer(ssl))
            switch connection.verificationCallback!(verificationResult, cert) {
            case .certificateVerified:
                return 1
            case .failed:
                return 0
            }
        }
    }

    func setCustomVerificationCallback(_ callbackManager: CustomVerifyManager) {
        // Store the verification callback. We need to do this to keep it alive throughout the connection.
        // We'll drop this when we're told that it's no longer needed to ensure we break the reference cycles
        // that this callback inevitably produces.
        self.customVerificationManager = callbackManager

        // We need to know what the current mode is.
        // Note that this also has the effect of ensuring that if we disabled certificate validation
        // it actually _stays_ disabled: if the verify mode is no-verification, this callback never gets called.
        let currentMode = CNIOBoringSSL_SSL_get_verify_mode(self.ssl)
        CNIOBoringSSL_SSL_set_custom_verify(self.ssl, currentMode) { ssl, outAlert in
            guard let unwrappedSSL = ssl else {
                preconditionFailure(
                    "Unexpected null pointer in custom verification callback. ssl: \(String(describing: ssl))"
                )
            }

            // Ok, this call may be a resumption of a previous negotiation. We need to check if our connection object has a pre-existing verifiation state.
            let connection = SSLConnection.loadConnectionFromSSL(unwrappedSSL)

            // We force unwrap the custom verification manager because for it to not be set is a programmer error.
            return connection.customVerificationManager!.process(on: connection)
        }
    }
    func setQuicDelegate(_ delegate:any NIOSSLQuicDelegate) {
        self.quicDelegate = delegate
        self.mode = .quic
            
        // Register our SSL_QUIC_Method Callbacks / Handlers
        precondition(CNIOBoringSSL_SSL_set_quic_method(self.ssl, &quicMethods) == 1, "SSLConnection::QUIC Error - Failed to register QUIC Method Handlers")

        // If we're using legacy QUIC params, let BoringSSL know
        if delegate.useLegacyQuicParams {
            CNIOBoringSSL_SSL_set_quic_use_legacy_codepoint(self.ssl, 1)
        }

        // Grab this Connections QUIC Params
        var quicParams = delegate.ourParams
        //print("SSLConnection:: Injecting QUIC Params into SSL -> \(quicParams.hexString)")
        
        // Pass our QUIC Params onto BoringSSL
        precondition(CNIOBoringSSL_SSL_set_quic_transport_params(self.ssl, &quicParams, quicParams.count) == 1, "SSLConnection::QUIC Error - Failed to set QUIC Params")
    }

    /// Sets whether renegotiation is supported.
    func setRenegotiationSupport(_ state: NIORenegotiationSupport) {
        var baseState: ssl_renegotiate_mode_t

        switch state {
        case .none:
            baseState = ssl_renegotiate_never
        case .once:
            baseState = ssl_renegotiate_once
        case .always:
            baseState = ssl_renegotiate_freely
        }

        CNIOBoringSSL_SSL_set_renegotiate_mode(self.ssl, baseState)
    }

    /// Performs hostname validation against the peer certificate using the configured server name.
    func validateHostname(address: SocketAddress) throws {
        // We want the leaf certificate.
        guard let peerCert = self.getPeerCertificate() else {
            throw NIOSSLError.noCertificateToValidate
        }

        guard
            try validIdentityForService(
                serverHostname: self.expectedHostname,
                socketAddress: address,
                leafCertificate: peerCert
            )
        else {
            throw NIOSSLExtraError.failedToValidateHostname(expectedName: self.expectedHostname ?? "<none>")
        }
    }

    /// Spins the handshake state machine and performs the next step of the handshake
    /// protocol.
    ///
    /// This method may write data into internal buffers that must be sent: call
    /// `getDataForNetwork` after this method is called. This method also consumes
    /// data from internal buffers: call `consumeDataFromNetwork` before calling this
    /// method.
    func doHandshake() -> AsyncOperationResult<CInt> {
        CNIOBoringSSL_ERR_clear_error()
        let rc = CNIOBoringSSL_SSL_do_handshake(ssl)

        if rc == 1 {
            return .complete(rc)
        }

        let result = CNIOBoringSSL_SSL_get_error(ssl, rc)
        let error = BoringSSLError.fromSSLGetErrorResult(result)!

        switch error {
        case .wantRead,
            .wantWrite,
            .wantCertificateVerify,
            .wantX509Lookup:
            return .incomplete
        default:
            return .failed(error)
        }
    }

    /// Spins the shutdown state machine and performs the next step of the shutdown
    /// protocol.
    ///
    /// This method may write data into internal buffers that must be sent: call
    /// `getDataForNetwork` after this method is called. This method also consumes
    /// data from internal buffers: call `consumeDataFromNetwork` before calling this
    /// method.
    func doShutdown() -> AsyncOperationResult<CInt> {
        CNIOBoringSSL_ERR_clear_error()
        let rc = CNIOBoringSSL_SSL_shutdown(ssl)

        switch rc {
        case 1:
            return .complete(rc)
        case 0:
            return .incomplete
        default:
            let result = CNIOBoringSSL_SSL_get_error(ssl, rc)
            let error = BoringSSLError.fromSSLGetErrorResult(result)!

            switch error {
            case .wantRead,
                .wantWrite:
                return .incomplete
            default:
                return .failed(error)
            }
        }
    }

    /// Given some unprocessed data from the remote peer, places it into
    /// BoringSSL's receive buffer ready for handling by BoringSSL.
    ///
    /// This method should be called whenever data is received from the remote
    /// peer. It must be immediately followed by an I/O operation, e.g. `readDataFromNetwork`
    /// or `doHandshake` or `doShutdown`.
    func consumeDataFromNetwork(_ data: ByteBuffer) {
//        self.bio!.receiveFromNetwork(buffer: data)
        switch self.mode {
        case .classic:
            self.bio!.receiveFromNetwork(buffer: data)
        case .quic:
            //var d = Array(data.readableBytesView)
            // We expect only valid QUIC Crypto Frames (0x06<offset><length><data of length length>)
            guard var d = data.getQuicCryptoFrame() else {
                //self.parentHandler?.fireErrorCaught(Errors.invalidQuicCryptoFrame)
                print("SSLConnection::Invalid QuicCryptoFrame")
                print(data.readableBytesView.hexString)
                return
            }
            
            assert(CNIOBoringSSL_SSL_provide_quic_data(self.ssl, self.epoch, &d, d.count) == 1)
            
            if self.hasProvidedPeersParams == false {
                if self.epoch == ssl_encryption_handshake {
                    var peerParams:UnsafePointer<UInt8>? = nil
                    var peerParamsLength:Int = 0
                    CNIOBoringSSL_SSL_get_peer_quic_transport_params(self.ssl, &peerParams, &peerParamsLength)
                    if peerParamsLength > 0 {
                        self.hasProvidedPeersParams = true
                        self.quicDelegate?.onPeerParams(params: Array(UnsafeBufferPointer(start: peerParams, count: peerParamsLength)))
                    }
                }
            }
        }
    }

    /// Obtains some encrypted data ready for the network from BoringSSL.
    ///
    /// This call obtains only data that BoringSSL has already written into its send
    /// buffer. As a result, it should be called last, after all other operations have
    /// been performed, to allow BoringSSL to write as much data as necessary into the
    /// `BIO`.
    ///
    /// Returns `nil` if there is no data to write. Otherwise, returns all of the pending
    /// data.
    func getDataForNetwork() -> ByteBuffer? {
        self.bio!.outboundCiphertext()
    }

    /// Attempts to decrypt any application data sent by the remote peer, and fills a buffer
    /// containing the cleartext bytes.
    ///
    /// This method can only consume data previously fed into BoringSSL in `consumeDataFromNetwork`.
    func readDataFromNetwork(outputBuffer: inout ByteBuffer) -> AsyncOperationResult<Int> {
        // TODO(cory): It would be nice to have an withUnsafeMutableWriteableBytes here, but we don't, so we
        // need to make do with writeWithUnsafeMutableBytes instead. The core issue is that we can't
        // safely return any of the error values that SSL_read might provide here because writeWithUnsafeMutableBytes
        // will try to use that as the number of bytes written and blow up. If we could prevent it doing that (which
        // we can with reading) that would be grand, but we can't, so instead we need to use a temp variable. Not ideal.
        //
        // We require that there is space to write at least one TLS record.
        var bytesRead: CInt = 0
        let rc = outputBuffer.writeWithUnsafeMutableBytes(minimumWritableBytes: SSL_MAX_RECORD_SIZE) {
            (pointer) -> Int in
            // We ask for the amount of spare space in the buffer, clamping to CInt.max.
            let maxReadSize = Int(CInt.max)
            let readSize = CInt(min(maxReadSize, pointer.count))
            bytesRead = CNIOBoringSSL_SSL_read(self.ssl, pointer.baseAddress, readSize)
            return bytesRead >= 0 ? Int(bytesRead) : 0
        }

        if bytesRead > 0 {
            return .complete(rc)
        } else {
            let result = CNIOBoringSSL_SSL_get_error(ssl, CInt(bytesRead))
            let error = BoringSSLError.fromSSLGetErrorResult(result)!

            switch error {
            case .wantRead,
                .wantWrite:
                return .incomplete
            default:
                return .failed(error)
            }
        }
    }

    /// Encrypts cleartext application data ready for sending on the network.
    ///
    /// This call will only write the data into BoringSSL's internal buffers. It needs to be obtained
    /// by calling `getDataForNetwork` after this call completes.
    func writeDataToNetwork(_ data: inout ByteBuffer) -> AsyncOperationResult<CInt> {
        // BoringSSL does not allow calling SSL_write with zero-length buffers. Zero-length
        // writes always succeed.
        guard data.readableBytes > 0 else {
            return .complete(0)
        }

        let writtenBytes = data.withUnsafeReadableBytes { (pointer) -> CInt in
            CNIOBoringSSL_SSL_write(ssl, pointer.baseAddress, CInt(pointer.count))
        }

        if writtenBytes > 0 {
            // The default behaviour of SSL_write is to only return once *all* of the data has been written,
            // unless the underlying BIO cannot satisfy the need (in which case WANT_WRITE will be returned).
            // We're using our BIO, which is always writable, so WANT_WRITE cannot fire so we'd always
            // expect this to write the complete quantity of readable bytes in our buffer.
            precondition(writtenBytes == data.readableBytes)
            data.moveReaderIndex(forwardBy: Int(writtenBytes))
            return .complete(writtenBytes)
        } else {
            let result = CNIOBoringSSL_SSL_get_error(ssl, writtenBytes)
            let error = BoringSSLError.fromSSLGetErrorResult(result)!

            switch error {
            case .wantRead, .wantWrite:
                return .incomplete
            default:
                return .failed(error)
            }
        }
    }
    // This requests the parentHandler (NIOSSLHandler) to perform a flush. That flush then calls `getDataForNetwork` on this connection.
    func flush() {
        self.parentHandler!.flush()
    }
    /// Returns the protocol negotiated via ALPN, if any. Returns `nil` if no protocol
    /// was negotiated.
    func getAlpnProtocol() -> String? {
        var protoName = UnsafePointer<UInt8>(bitPattern: 0)
        var protoLen: CUnsignedInt = 0

        CNIOBoringSSL_SSL_get0_alpn_selected(ssl, &protoName, &protoLen)
        guard protoLen > 0 else {
            return nil
        }

        return String(decoding: UnsafeBufferPointer(start: protoName, count: Int(protoLen)), as: UTF8.self)
    }

    /// Get the leaf certificate from the peer certificate chain as a managed object,
    /// if available.
    func getPeerCertificate() -> NIOSSLCertificate? {
        guard let certPtr = CNIOBoringSSL_SSL_get_peer_certificate(ssl) else {
            return nil
        }

        return NIOSSLCertificate.fromUnsafePointer(takingOwnership: certPtr)
    }

    /// Drops persistent connection state.
    ///
    /// Must only be called when the connection is no longer needed. The rest of this object
    /// preconditions on that being true, so we'll find out quickly when that's not the case.
    func close() {
        /// Drop the verification callbacks. This breaks any reference cycles that are inevitably
        /// created by these callbacks.
        self.verificationCallback = nil
        self.customVerificationManager = nil

        // Also drop the reference to the parent channel handler, which is a trivial reference cycle.
        self.parentHandler = nil

        // And finally drop the data stored by the bytebuffer BIO
        self.bio?.close()
    }

    /// Retrieves any inbound data that has not been processed by BoringSSL.
    ///
    /// When unwrapping TLS from a connection, there may be application bytes that follow the terminating
    /// CLOSE_NOTIFY message. Those bytes may have been passed to this `SSLConnection`, and so we need to
    /// retrieve them.
    ///
    /// This function extracts those bytes and returns them to the user. This should only be called when
    /// the connection has been shutdown.
    ///
    /// - returns: The unconsumed `ByteBuffer`, if any.
    func extractUnconsumedData() -> ByteBuffer? {
        self.bio?.evacuateInboundData()
    }

    /// Returns  an optional `TLSVersion` used on a `Channel` through the `NIOSSLHandler` APIs.
    func getTLSVersionForConnection() -> TLSVersion? {
        let uint16Version = CNIOBoringSSL_SSL_version(self.ssl)
        switch uint16Version {
        case TLS1_3_VERSION:
            return .tlsv13
        case TLS1_2_VERSION:
            return .tlsv12
        case TLS1_1_VERSION:
            return .tlsv11
        case TLS1_VERSION:
            return .tlsv1
        default:
            return nil
        }
    }
}
// BoringSSL QUIC Methods
extension SSLConnection {
    //set_read_secret: (@convention(c) (OpaquePointer?, ssl_encryption_level_t, OpaquePointer?, UnsafePointer<UInt8>?, Int) -> Int32)!,
    static func setReadSecret (_ ctx: OpaquePointer?, _ level: ssl_encryption_level_t, _ cipherPtr: OpaquePointer?, _ secretPtr: UnsafePointer<UInt8>?, _ secretLength: Int) -> Int32 {
        guard let ctx = ctx else { print("set_read_secret called with nil SSLContext"); return 0 }
        let conn = SSLConnection.loadConnectionFromSSL(ctx)
        if conn.epoch.rawValue < level.rawValue { conn.epoch = level }
        conn.quicDelegate?.onReadSecret(
            epoch: level.rawValue,
            cipherSuite: CNIOBoringSSL_SSL_CIPHER_get_protocol_id(cipherPtr),
            secret: Array(UnsafeBufferPointer<UInt8>(start: secretPtr, count: secretLength))
        )
        return 1
    }
    
    //set_write_secret: (@convention(c) (OpaquePointer?, ssl_encryption_level_t, OpaquePointer?, UnsafePointer<UInt8>?, Int) -> Int32)!,
    static func setWriteSecret(_ ctx: OpaquePointer?, _ level: ssl_encryption_level_t, _ cipherPtr: OpaquePointer?, _ secretPtr: UnsafePointer<UInt8>?, _ secretLength: Int) -> Int32 {
        guard let ctx = ctx else { print("set_write_secret called with nil SSLContext"); return 0 }
        let conn = SSLConnection.loadConnectionFromSSL(ctx)
        conn.quicDelegate?.onWriteSecret(
            epoch: level.rawValue,
            cipherSuite: CNIOBoringSSL_SSL_CIPHER_get_protocol_id(cipherPtr),
            secret: Array(UnsafeBufferPointer<UInt8>(start: secretPtr, count: secretLength))
        )
        return 1
    }
    
    //add_handshake_data: (@convention(c) (OpaquePointer?, ssl_encryption_level_t, UnsafePointer<UInt8>?, Int) -> Int32)!,
    static func addHandshakeData(_ ctx: OpaquePointer?, _ level: ssl_encryption_level_t, _ dataPtr: UnsafePointer<UInt8>?, _ length: Int) -> Int32 {
        guard let ctx = ctx else { print("add_handshake_data called with nil SSLContext"); return 0 }
        let conn = SSLConnection.loadConnectionFromSSL(ctx)
        print("SSLConnection::AddHandshakeData - Called")
        // We prefix the handshake data with a crypto frame header so we can parse / identify this data further up the pipeline
        // Does this method only get called with complete frames? or should we wait to prefix the data until flushFlight is called?
        conn.outboundQueue.writeBytes([0x06, 0x00] + writeQuicVarInt(UInt64(length)))
        conn.outboundQueue.writeBytes(UnsafeBufferPointer<UInt8>(start: dataPtr, count: length))
        return 1
    }
    
    //flush_flight: (@convention(c) (OpaquePointer?) -> Int32)!,
    static func flushFlight(_ ctx: OpaquePointer?) -> Int32 {
        guard let ctx = ctx else { print("flush_flight called with nil SSLContext"); return 0 }
        let conn = SSLConnection.loadConnectionFromSSL(ctx)
        print("SSLConnection::FlushFlight - Called")
        conn.flush()
        return 1
    }
    
    //send_alert: (@convention(c) (OpaquePointer?, ssl_encryption_level_t, UInt8) -> Int32)!
    static func sendAlert(_ ctx: OpaquePointer?, _ level: ssl_encryption_level_t, _ int:UInt8) -> Int32 {
        guard let ctx = ctx else { print("send_alert called with nil SSLContext"); return 0 }
        let _ = SSLConnection.loadConnectionFromSSL(ctx)
        print("SSLConnection::SendAlert - Called - \(int)")
        return 1
    }
    
    // Allows installing Quic Params on inbound connections
    static func setQuicParams(_ params:[UInt8], ctx: OpaquePointer) {
        var p = params
        precondition(CNIOBoringSSL_SSL_set_quic_transport_params(ctx, &p, p.count) == 1)
    }
    
    private static func writeQuicVarInt(_ num: UInt64, minBytes: Int = 0) -> [UInt8] {
        func getLength(_ bytes: Int) -> UInt8 {
          switch bytes {
            case 1: return 0
            case 2: return 1
            case 3, 4: return 2
            case 5...8: return 3
            default: return 0
          }
        }

        var bytes: [UInt8] = num.bytes(minBytes: minBytes)
        guard !bytes.isEmpty else { return [0] }

        let length = getLength(bytes.count)
        if (bytes[0] >> 6) == 0 && (minBytes <= bytes.count) {
          // encode the length in the two available bits
          bytes[0] ^= (UInt8(length) << 6)
        } else {
          // add a new byte to store the length
          bytes.insert(UInt8(length + 1) << 6, at: 0)
        }
        return bytes
    }
}
private extension UInt64 {
    func bytes(minBytes:Int = 0, bigEndian:Bool = true) -> [UInt8] {
        var bytes = Swift.withUnsafeBytes(of: bigEndian ? self.bigEndian : self.littleEndian, Array.init)
        while !bytes.isEmpty && bytes[0] == 0 && bytes.count > minBytes { bytes.removeFirst() }
        return bytes
    }
}
/// MARK: ConnectionRole
extension SSLConnection {
    internal enum ConnectionRole {
        case server
        case client
    }
}

// MARK: Certificate Peer Chain Buffers
extension SSLConnection {
    /// A collection of buffers representing the DER-encoded bytes of the peer certificate chain.
    struct PeerCertificateChainBuffers {
        private let basePointer: OpaquePointer

        fileprivate init(basePointer: OpaquePointer) {
            self.basePointer = basePointer
        }
    }

    /// Invokes a block with a collection of pointers to DER-encoded bytes of the peer certificate chain.
    ///
    /// The pointers are only guaranteed to be valid for the duration of this call: it is undefined behaviour to escape
    /// any of these pointers from the block, or the certificate iterator itself from the block. Users must either use the
    /// bytes synchronously within the block, or they must copy them to a new buffer that they own.
    ///
    /// If there are no peer certificates, the body will be called with nil.
    func withPeerCertificateChainBuffers<Result>(
        _ body: (PeerCertificateChainBuffers?) throws -> Result
    ) rethrows -> Result {
        guard let stackPointer = CNIOBoringSSL_SSL_get0_peer_certificates(self.ssl) else {
            return try body(nil)
        }

        return try body(PeerCertificateChainBuffers(basePointer: stackPointer))
    }

    /// The certificate chain presented by the peer.
    func peerCertificateChain() throws -> [NIOSSLCertificate] {
        try self.withPeerCertificateChainBuffers { buffers in
            guard let buffers = buffers else {
                return []
            }

            return try buffers.map { try NIOSSLCertificate(bytes: $0, format: .der) }
        }
    }
}

extension SSLConnection.PeerCertificateChainBuffers: RandomAccessCollection {
    struct Index: Hashable, Comparable, Strideable {
        typealias Stride = Int

        fileprivate var index: Int

        fileprivate init(_ index: Int) {
            self.index = index
        }

        static func < (lhs: Index, rhs: Index) -> Bool {
            lhs.index < rhs.index
        }

        func advanced(
            by n: SSLConnection.PeerCertificateChainBuffers.Index.Stride
        ) -> SSLConnection.PeerCertificateChainBuffers.Index {
            var result = self
            result.index += n
            return result
        }

        func distance(
            to other: SSLConnection.PeerCertificateChainBuffers.Index
        ) -> SSLConnection.PeerCertificateChainBuffers.Index.Stride {
            other.index - self.index
        }
    }

    typealias Element = UnsafeRawBufferPointer

    var startIndex: Index {
        Index(0)
    }

    var endIndex: Index {
        Index(self.count)
    }

    var count: Int {
        CNIOBoringSSL_sk_CRYPTO_BUFFER_num(self.basePointer)
    }

    subscript(_ index: Index) -> UnsafeRawBufferPointer {
        precondition(index < self.endIndex)
        guard let ptr = CNIOBoringSSL_sk_CRYPTO_BUFFER_value(self.basePointer, index.index) else {
            preconditionFailure("Unable to locate backing pointer.")
        }
        guard let dataPointer = CNIOBoringSSL_CRYPTO_BUFFER_data(ptr) else {
            preconditionFailure("Unable to retrieve data pointer from crypto_buffer")
        }
        let byteCount = CNIOBoringSSL_CRYPTO_BUFFER_len(ptr)

        // We want an UnsafeRawBufferPointer here, so we need to erase the pointer type.
        let bufferDataPointer = UnsafeBufferPointer(start: dataPointer, count: byteCount)
        return UnsafeRawBufferPointer(bufferDataPointer)
    }
}

// MARK: Helpers for managing ex_data
extension SSLConnection {
    // Loads an SSLConnection from an SSL*. Does not take ownership of the pointer.
    static func loadConnectionFromSSL(_ ssl: OpaquePointer) -> SSLConnection {
        guard let connectionPointer = CNIOBoringSSL_SSL_get_ex_data(ssl, sslConnectionExDataIndex) else {
            // Uh-ok, our application state is gone. Don't let this error silently pass, go bang.
            preconditionFailure("Unable to find application data from SSL * \(ssl), index \(sslConnectionExDataIndex)")
        }

        return Unmanaged<SSLConnection>.fromOpaque(connectionPointer).takeUnretainedValue()
    }
}

private extension ByteBuffer {
    func getQuicVarInt(at offset: Int) -> (length:Int, value:UInt64)? {
        // first two bits of the first byte.
        guard let vByte = self.getBytes(at: offset, length: 1)?.first else { print("NIOSSLConnection::GetQuicVarInt::Not Enough Bytes Available"); return nil }
        var v = UInt64(vByte)
        let prefix = v >> 6
        let length = (1 << prefix) - 1
        
        // Make sure we have enough bytes before we start forcefully unwrapping below...
        guard self.readableBytes >= (offset - self.readerIndex) + length else { print("NIOSSLConnection::GetQuicVarInt::Not Enough Bytes Available - Offset: \(offset - self.readerIndex) + Length: \(length)"); return nil }
        
        // Once the length is known, remove these bits and read any remaining bytes.
        v = v & 0x3f
        for i in 0..<length {
            v = (v << 8) + UInt64(self.getBytes(at: offset + i + 1, length: 1)![0])
        }
        
        return (length + 1, v)
    }
    
    func getQuicCryptoFrame() -> [UInt8]? {
        guard self.getBytes(at: self.readerIndex, length: 1)?.first == 0x06 else { return nil }
        guard let offset = self.getQuicVarInt(at: self.readerIndex + 1) else { return nil }
        guard let length = self.getQuicVarInt(at: self.readerIndex + 1 + offset.length) else { return nil }
        guard self.readableBytes == 1 + offset.length + length.length + Int(length.value) else { return nil }
        return self.getBytes(at: self.readerIndex + 1 + offset.length + length.length, length: Int(length.value))
    }
}

private extension ByteBufferView {
    var hexString:String {
        self.map({ var h = String($0, radix: 16); h = h.count == 1 ? "0"+h : h; return h }).joined()
    }
}

private extension Array where Element == UInt8 {
    var hexString:String {
        self.map({ var h = String($0, radix: 16); h = h.count == 1 ? "0"+h : h; return h }).joined()
    }
}
