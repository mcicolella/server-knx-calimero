/*
    Calimero 2 - A library for KNX network access
    Copyright (c) 2010, 2011 B. Malinowsky

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package tuwien.auto.calimero.knxnetip;

import java.io.IOException;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.InetAddress;
import java.net.InetSocketAddress;

import tuwien.auto.calimero.CloseEvent;
import tuwien.auto.calimero.exception.KNXException;
import tuwien.auto.calimero.exception.KNXFormatException;
import tuwien.auto.calimero.exception.KNXIllegalArgumentException;
import tuwien.auto.calimero.exception.KNXIllegalStateException;
import tuwien.auto.calimero.exception.KNXInvalidResponseException;
import tuwien.auto.calimero.exception.KNXRemoteException;
import tuwien.auto.calimero.exception.KNXTimeoutException;
import tuwien.auto.calimero.knxnetip.servicetype.ConnectRequest;
import tuwien.auto.calimero.knxnetip.servicetype.ConnectResponse;
import tuwien.auto.calimero.knxnetip.servicetype.ConnectionstateRequest;
import tuwien.auto.calimero.knxnetip.servicetype.ConnectionstateResponse;
import tuwien.auto.calimero.knxnetip.servicetype.DisconnectRequest;
import tuwien.auto.calimero.knxnetip.servicetype.DisconnectResponse;
import tuwien.auto.calimero.knxnetip.servicetype.ErrorCodes;
import tuwien.auto.calimero.knxnetip.servicetype.KNXnetIPHeader;
import tuwien.auto.calimero.knxnetip.servicetype.PacketHelper;
import tuwien.auto.calimero.knxnetip.servicetype.ServiceAck;
import tuwien.auto.calimero.knxnetip.util.CRI;
import tuwien.auto.calimero.knxnetip.util.HPAI;
import tuwien.auto.calimero.log.LogLevel;
import tuwien.auto.calimero.log.LogManager;

/**
 * Base implementation for client tunneling, device management, and routing.
 * <p>
 * The communication on OSI layer 4 is done with UDP.<br>
 * Implements a communication heartbeat monitor.
 * 
 * @author B. Malinowsky
 */
abstract class ClientConnection extends ConnectionBase
{
	// IMPLEMENTATION NOTE: on MS Windows platforms, interruptible I/O is not supported,
	// i.e., a blocked I/O method remains blocked after interrupt of the thread.
	// To bypass this, we use the rude way to close I/O to force
	// these methods to interrupt and throw.

	/**
	 * Status code of communication: waiting for cEMI confirmation after receive service
	 * acknowledgment, no error, not ready to send.
	 * <p>
	 */
	public static final int CEMI_CON_PENDING = 4;

	/**
	 * Status code of communication: unknown error, no send possible.
	 * <p>
	 */
	public static final int UNKNOWN_ERROR = -1;

	// request to confirmation timeout
	private static final int CONFIRMATION_TIMEOUT = 3;

	private HeartbeatMonitor heartbeat;

	// additional textual information about connection status
	// only set on some errors in receiver, check before using it
	private String status = "";

	private volatile boolean cleanup;

	// logger is initialized in connect, when name of connection is available
	ClientConnection(final int serviceRequest, final int serviceAck,
		final int maxSendAttempts, final int responseTimeout)
	{
		super(serviceRequest, serviceAck, maxSendAttempts, responseTimeout);
	}

	/**
	 * Opens a new IP communication channel to a remote server.
	 * <p>
	 * The communication state of this object is assumed to be closed state. This method
	 * is designed to be called only once during the objects lifetime!
	 * 
	 * @param localEP the local endpoint to use for communication channel
	 * @param serverCtrlEP the remote server control endpoint used for connect request
	 * @param cri connect request information used to configure the communication
	 *        attributes
	 * @param useNAT <code>true</code> to use a NAT (network address translation) aware
	 *        communication mechanism, <code>false</code> to use the default way
	 * @throws KNXException on socket communication error
	 * @throws KNXTimeoutException on no connect response before connect timeout
	 * @throws KNXRemoteException if response indicates an error condition at the server
	 *         concerning the request
	 * @throws KNXInvalidResponseException if connect response is in wrong format
	 * @throws InterruptedException on interrupted thread during connect, all resources
	 *         are cleaned up before passing on this exception
	 */
	protected void connect(final InetSocketAddress localEP, final InetSocketAddress serverCtrlEP,
		final CRI cri, final boolean useNAT) throws KNXException, InterruptedException
	{
		if (state != CLOSED)
			throw new KNXIllegalStateException("open connection");
		ctrlEndpt = serverCtrlEP;
		if (ctrlEndpt.isUnresolved())
			throw new KNXException("server control endpoint is unresolved: " + serverCtrlEP);
		useNat = useNAT;
		logger = LogManager.getManager().getLogService(getName());
		Exception thrown = null;
		try {
			// if we allow localEP to be null, we would create an unbound socket
			if (localEP == null)
				throw new KNXIllegalArgumentException("no local endpoint specified");
			socket = new DatagramSocket(localEP);
			ctrlSocket = socket;

			logger.info("establish connection from " + socket.getLocalSocketAddress()
				+ " to " + ctrlEndpt);
			// HPAI throws if wildcard local address (0.0.0.0) is supplied
			final HPAI hpai = new HPAI(HPAI.IPV4_UDP, useNat ? null
				: (InetSocketAddress) socket.getLocalSocketAddress());
			final byte[] buf = PacketHelper.toPacket(new ConnectRequest(cri, hpai, hpai));
			final DatagramPacket p = new DatagramPacket(buf, buf.length, ctrlEndpt.getAddress(),
					ctrlEndpt.getPort());
			ctrlSocket.send(p);
		}
		catch (final IOException e) {
			thrown = e;
		}
		catch (final SecurityException e) {
			thrown = e;
		}
		if (thrown != null) {
			if (socket != null)
				socket.close();
			logger.error("communication failure on connect", thrown);
			if (localEP.getAddress().isLoopbackAddress())
				logger.warn("try to specify the actual IP address of the local host");
			LogManager.getManager().removeLogService(logger.getName());
			throw new KNXException("on connect to " + serverCtrlEP + ": " + thrown.getMessage());
		}

		logger.info("wait for connect response from " + ctrlEndpt + " ...");
		startReceiver();
		try {
			final boolean changed = waitForStateChange(CLOSED, CONNECT_REQ_TIMEOUT);
			if (state == OK) {
				(heartbeat = new HeartbeatMonitor()).start();
				logger.info("connection established");
				return;
			}
			final KNXException e;
			if (!changed)
				e = new KNXTimeoutException("timeout connecting to control endpoint " + ctrlEndpt);
			else if (state == ACK_ERROR)
				e = new KNXRemoteException("error response from control endpoint " + ctrlEndpt
						+ ", " + status);
			else
				e = new KNXInvalidResponseException("invalid connect response from " + ctrlEndpt);
			// quit, cleanup and notify user
			connectCleanup(e);
			throw e;
		}
		catch (final InterruptedException e) {
			connectCleanup(e);
			throw e;
		}
	}

	protected void cleanup(final int initiator, final String reason, final LogLevel level,
		final Throwable t)
	{
		// we want close/cleanup be called only once
		synchronized (this) {
			if (cleanup)
				return;
			cleanup = true;
		}

		logger.log(level, "close connection - " + reason, t);
		// heartbeat was not necessarily used at all
		if (heartbeat != null)
			heartbeat.quit();
		stopReceiver();
		socket.close();
		// ensure user sees final state CLOSED
		updateState = true;
		super.cleanup(initiator, reason, level, t);
	}

	/* (non-Javadoc)
	* @see tuwien.auto.calimero.knxnetip.ConnectionBase#doExtraBlockingModes()
	*/
	void doExtraBlockingModes() throws KNXTimeoutException, InterruptedException
	{
		// blocking mode is wait for .con
		// wait for incoming request with confirmation
		waitForStateChange(ClientConnection.CEMI_CON_PENDING,
			ClientConnection.CONFIRMATION_TIMEOUT);
		// throw on no answer
		if (internalState == ClientConnection.CEMI_CON_PENDING) {
			final KNXTimeoutException e = new KNXTimeoutException("no confirmation reply received");
			logger.log(LogLevel.INFO, "response timeout waiting for confirmation", e);
			internalState = OK;
			throw e;
		}
	}

	/**
	 * @see tuwien.auto.calimero.knxnetip.ConnectionBase#handleServiceType
	 *      (tuwien.auto.calimero.knxnetip.servicetype.KNXnetIPHeader, byte[], int,
	 *      java.net.InetAddress, int)
	 * @throws IOException
	 */
	protected boolean handleServiceType(final KNXnetIPHeader h, final byte[] data,
		final int offset, final InetAddress src, final int port) throws KNXFormatException,
		IOException
	{
		final int svc = h.getServiceType();
		if (svc == KNXnetIPHeader.CONNECT_REQ)
			logger.warn("received connect request - ignored");
		else if (svc == KNXnetIPHeader.CONNECT_RES) {
			final ConnectResponse res = new ConnectResponse(data, offset);
			// we do an additional check for UDP to be on the safe side
			// endpoint is only != null on no error
			final HPAI ep = res.getDataEndpoint();
			if (res.getStatus() == ErrorCodes.NO_ERROR
				&& ep.getHostProtocol() == HPAI.IPV4_UDP) {
				channelId = res.getChannelID();
				final InetAddress ip = ep.getAddress();
				// in NAT aware mode, if the data EP is incomplete or left
				// empty, we fall back to the IP address and port of the sender
				if (useNat && (ip == null || ip.isAnyLocalAddress() || ep.getPort() == 0)) {
					dataEndpt = new InetSocketAddress(src, port);
					logger.info("NAT aware mode: using server data endpoint " + dataEndpt);
				}
				else {
					dataEndpt = new InetSocketAddress(ip, ep.getPort());
					logger.info("using server-assigned data endpoint " + dataEndpt);
				}
				checkVersion(h);
				setStateNotify(OK);
				return true;
			}
			if (ep != null && ep.getHostProtocol() != HPAI.IPV4_UDP)
				logger.error(status = "server does not agree with UDP/IP");
			else
				logger.error(status = res.getStatusString());
			setStateNotify(ACK_ERROR);
		}
		else if (svc == KNXnetIPHeader.CONNECTIONSTATE_REQ)
			logger.warn("received connection state request - ignored");
		else if (svc == KNXnetIPHeader.CONNECTIONSTATE_RES) {
			if (checkVersion(h))
				heartbeat.setResponse(new ConnectionstateResponse(data, offset));
		}
		else if (svc == KNXnetIPHeader.DISCONNECT_REQ) {
			if (ctrlEndpt.getAddress().equals(src) && ctrlEndpt.getPort() == port)
				disconnectRequested(new DisconnectRequest(data, offset));
		}
		else if (svc == KNXnetIPHeader.DISCONNECT_RES) {
			final DisconnectResponse res = new DisconnectResponse(data, offset);
			if (res.getStatus() != ErrorCodes.NO_ERROR)
				logger.warn("received disconnect response status 0x"
						+ Integer.toHexString(res.getStatus()) + " ("
						+ ErrorCodes.getErrorMessage(res.getStatus()) + ")");
			// finalize closing
			closing = 2;
			setStateNotify(CLOSED);
		}
		else if (svc == serviceAck) {
			final ServiceAck res = new ServiceAck(svc, data, offset);
			if (!checkChannelId(res.getChannelID(), "acknowledgment"))
				return true;
			if (res.getSequenceNumber() != getSeqSend())
				logger.warn("received service acknowledgment with wrong send sequence "
						+ res.getSequenceNumber() + ", expected " + getSeqSend() + " - ignored");
			else {
				if (!checkVersion(h))
					return true;
				incSeqSend();
				// update state and notify our lock
				setStateNotify(res.getStatus() == ErrorCodes.NO_ERROR ? CEMI_CON_PENDING
						: ACK_ERROR);
				if (internalState == ACK_ERROR)
					logger.warn("received service acknowledgment status " + res.getStatusString());
			}
		}
		else
			return false;
		return true;
	}

	private void disconnectRequested(final DisconnectRequest req)
	{
		// requests with wrong channel ID are ignored (conforming to spec)
		if (req.getChannelID() == channelId) {
			final byte[] buf = PacketHelper.toPacket(new DisconnectResponse(channelId,
					ErrorCodes.NO_ERROR));
			final DatagramPacket p = new DatagramPacket(buf, buf.length, ctrlEndpt.getAddress(),
					ctrlEndpt.getPort());
			try {
				ctrlSocket.send(p);
			}
			catch (final IOException e) {
				logger.error("communication failure", e);
			}
			finally {
				cleanup(CloseEvent.SERVER_REQUEST, "server request", LogLevel.INFO, null);
			}
		}
	}

	/**
	 * Checks for supported protocol version in KNX header.
	 * <p>
	 * On unsupported version,
	 * {@link ClientConnection#close(int, String, LogLevel, Throwable)} is invoked.
	 * 
	 * @param h KNX header to check
	 * @return <code>true</code> on supported version, <code>false</code> otherwise
	 */
	private boolean checkVersion(final KNXnetIPHeader h)
	{
		if (h.getVersion() != KNXNETIP_VERSION_10) {
			status = "protocol version changed";
			close(CloseEvent.INTERNAL, "protocol version changed", LogLevel.ERROR, null);
			return false;
		}
		return true;
	}

	private void connectCleanup(final Exception thrown)
	{
		stopReceiver();
		socket.close();
		setState(CLOSED);
		logger.error("establishing connection failed", thrown);
		LogManager.getManager().removeLogService(logger.getName());
	}

	private final class HeartbeatMonitor extends Thread
	{
		// client SHALL wait 10 seconds for a connection state response from server
		private static final int CONNECTIONSTATE_REQ_TIMEOUT = 10;
		private static final int HEARTBEAT_INTERVAL = 60;
		private static final int MAX_REQUEST_ATTEMPTS = 4;
		private boolean received;

		HeartbeatMonitor()
		{
			super("KNXnet/IP heartbeat monitor");
			setDaemon(true);
		}

		public void run()
		{
			final byte[] buf = PacketHelper.toPacket(new ConnectionstateRequest(channelId,
					new HPAI(HPAI.IPV4_UDP, useNat ? null : (InetSocketAddress) socket
							.getLocalSocketAddress())));
			final DatagramPacket p = new DatagramPacket(buf, buf.length, ctrlEndpt.getAddress(),
					ctrlEndpt.getPort());
			try {
				while (true) {
					Thread.sleep(HEARTBEAT_INTERVAL * 1000);
					int i = 0;
					for (; i < MAX_REQUEST_ATTEMPTS; i++) {
						logger.trace("sending connection state request, attempt " + (i + 1));
						synchronized (this) {
							received = false;
							socket.send(p);

							long remaining = CONNECTIONSTATE_REQ_TIMEOUT * 1000;
							final long end = System.currentTimeMillis() + remaining;
							while (!received && remaining > 0) {
								wait(remaining);
								remaining = end - System.currentTimeMillis();
							}
							if (received)
								break;
						}
					}
					// disconnect on no reply
					if (i == MAX_REQUEST_ATTEMPTS) {
						close(CloseEvent.INTERNAL, "no heartbeat response", LogLevel.WARN, null);
						break;
					}
				}
			}
			catch (final InterruptedException e) {
				// simply let this thread exit
			}
			catch (final IOException e) {
				close(CloseEvent.INTERNAL, "heartbeat communication failure", LogLevel.ERROR, e);
			}
		}

		void quit()
		{
			interrupt();
			if (currentThread() == this)
				return;
			try {
				join();
			}
			catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}

		void setResponse(final ConnectionstateResponse res)
		{
			final boolean ok = res.getStatus() == ErrorCodes.NO_ERROR;
			synchronized (this) {
				if (ok)
					received = true;
				notify();
			}
			if (!ok)
				logger.warn("connection state response status: " + res.getStatusString());
		}
	}
}
