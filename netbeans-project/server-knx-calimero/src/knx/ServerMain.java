package knx;


/*
    Calimero 2 - A library for KNX network access
    Copyright (c) 2010, 2013 B. Malinowsky

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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.EventListener;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import tuwien.auto.calimero.DataUnitBuilder;
import tuwien.auto.calimero.FrameEvent;
import tuwien.auto.calimero.GroupAddress;
import tuwien.auto.calimero.IndividualAddress;
import tuwien.auto.calimero.KNXAddress;
import tuwien.auto.calimero.Priority;
import tuwien.auto.calimero.buffer.Configuration;
import tuwien.auto.calimero.buffer.NetworkBuffer;
import tuwien.auto.calimero.buffer.StateFilter;
import tuwien.auto.calimero.cemi.CEMIFactory;
import tuwien.auto.calimero.cemi.CEMILData;
import tuwien.auto.calimero.datapoint.DatapointMap;
import tuwien.auto.calimero.datapoint.DatapointModel;
import tuwien.auto.calimero.exception.KNXException;
import tuwien.auto.calimero.exception.KNXFormatException;
import tuwien.auto.calimero.internal.EventListeners;
import tuwien.auto.calimero.knxnetip.KNXnetIPRouting;
import tuwien.auto.calimero.knxnetip.util.HPAI;
import tuwien.auto.calimero.link.KNXNetworkLink;
import tuwien.auto.calimero.link.KNXNetworkLinkIP;
import tuwien.auto.calimero.link.NetworkLinkListener;
import tuwien.auto.calimero.link.medium.KNXMediumSettings;
import tuwien.auto.calimero.link.medium.TPSettings;
import tuwien.auto.calimero.log.LogLevel;
import tuwien.auto.calimero.log.LogManager;
import tuwien.auto.calimero.log.LogStreamWriter;
import tuwien.auto.calimero.log.LogWriter;
import tuwien.auto.calimero.mgmt.PropertyAccess;
import tuwien.auto.calimero.mgmt.PropertyAccess.PID;
import tuwien.auto.calimero.server.InterfaceObject;
import tuwien.auto.calimero.server.InterfaceObjectServer;
import tuwien.auto.calimero.server.KNXPropertyException;
import tuwien.auto.calimero.server.gateway.KnxServerGateway;
import tuwien.auto.calimero.server.gateway.SubnetConnector;
import tuwien.auto.calimero.server.knxnetip.DefaultServiceContainer;
import tuwien.auto.calimero.server.knxnetip.KNXnetIPServer;
import tuwien.auto.calimero.server.knxnetip.RoutingServiceContainer;
import tuwien.auto.calimero.server.knxnetip.ServiceContainer;
import tuwien.auto.calimero.xml.Element;
import tuwien.auto.calimero.xml.KNXMLException;
import tuwien.auto.calimero.xml.XMLFactory;
import tuwien.auto.calimero.xml.XMLReader;

/**
 * Contains the startup code for the KNX server gateway.
 * <p>
 * Either use method {@link #main(String[])}, or {@link #ServerMain(LogWriter, String)} together
 * with {@link #run()}.
 * 
 * @author B. Malinowsky
 */
public class ServerMain implements Runnable
{
	/**
	 * Server configuration: specifies supported xml tags and attribute names.
	 * <p>
	 * See the example server configuration file for how to use them.
	 * <p>
	 */
	public static final class XmlConfiguration
	{
		/** */
		public static final String knxServer = "knxServer";
		/** */
		public static final String propDefs = "propertyDefinitionsResource";
		/** */
		public static final String svcCont = "serviceContainer";
		/** */
		public static final String dpRef = "datapointsRef";
		/** */
		public static final String subnet = "knxSubnet";
		/** */
		public static final String grpAddrFilter = "groupAddressFilter";
		/** */
		public static final String routingMcast = "routingMcast";

		/** */
		public static final String attrName = "name";
		/** */
		public static final String attrFriendly = "friendlyName";
		/** */
		public static final String attrRouting = "routing";
		/** */
		public static final String attrNetIf = "netIf";
		/** */
		public static final String attrUdpPort = "udpPort";
		/** */
		public static final String attrReuseEP = "reuseCtrlEP";
		/** */
		public static final String attrMonitor = "allowNetworkMonitoring";
		/**
		 * KNX subnet type, "ip" or "virtual"
		 */
		public static final String attrType = "type";
		/** */
		public static final String attrId = "id";
	}

	private final KNXnetIPServer server;
	private String name;
	private String friendlyName;

	private KnxServerGateway gw;

	private final LogWriter logger;

	private String propertyDefs;

	// the service containers the KNX server will host
	private final List svcContainers = new ArrayList();
	// virtual links locally used with the KNX server for KNX network subnet emulation
	private final List virtualLinks = new ArrayList();

	// the following lists contain information from a loaded configuration
	// to be supplied to the gateway
	// tells whether the service container connects to a virtual KNX subnet
	private final List virtualSubnet = new ArrayList();
	private final List subnetAddress = new ArrayList();
	private final List subnetPort = new ArrayList();

	private SubnetConnector[] gwConnectors;

	// list of group addresses used in the group address filter of the KNXnet/IP server
	// key: Service Container, value: List with GroupAddress entries
	private final Map groupAddressFilters = new HashMap();
	// in virtual KNX subnets, the subnetwork can be described by a datapoint model
	// key: ServiceContainer, value: DatapointModel
	private final Map subnetDatapoints = new HashMap();

	// are we directly started from main, allowing terminal-based termination
	private boolean terminal;

	/**
	 * Main entry routine for starting the KNX server gateway.
	 * <p>
	 * 
	 * @param args the file name or URI to the KNX server xml configuration
	 */
	public static void main(final String[] args)
	{
		// globally log everything to System.out
		final LogWriter w = LogStreamWriter.newUnformatted(LogLevel.ALL, System.out, true, false);
		if (args.length == 0) {
			w.write("", LogLevel.INFO, "supply file name/URI for the KNX server configuration");
			return;
		}
		try {
			final ServerMain sr = new ServerMain(w, args[0]);
			sr.terminal = true;
			sr.run();
		}
		catch (final KNXMLException e) {
			w.write("", LogLevel.ERROR, "loading configuration from " + args[0], e);
		}
	}

	/**
	 * ServerMain constructor
	 * 
	 * @param w a log writer
	 * @param configURI location/file of KNX server and gateway configuration
	 * @throws KNXMLException
	 */
	public ServerMain(final LogWriter w, final String configURI) throws KNXMLException
	{
		logger = w;
		LogManager.getManager().addWriter("", logger);
		readConfig(configURI);

		server = new KNXnetIPServer(name, friendlyName);
		// load property definitions
		final InterfaceObjectServer ios = server.getInterfaceObjectServer();
		if (propertyDefs != null)
			try {
				ios.loadDefinitions(verifyFilePath(configURI, propertyDefs));
			}
			catch (final KNXException e) {
				e.printStackTrace();
			}
		// setGroupAddressFilter(s);

		// output the configuration we use
		if (logger != null) {
			for (int i = 0; i < svcContainers.size(); i++) {
				final ServiceContainer sc = (ServiceContainer) svcContainers.get(i);
				
				logger.write("", LogLevel.INFO, "Service container " + sc.getName() + ": ");
				logger.write("", LogLevel.INFO, "  " + sc.getControlEndpoint() + " routing="
						+ (sc instanceof RoutingServiceContainer));
				
				final boolean virtual = ((Boolean) virtualSubnet.get(i)).booleanValue();
				final String v = virtual ? "  virtual " : "  ";
				logger.write("", LogLevel.INFO, v + "KNX subnet " + sc.getSubnetAddress()
						+ ", medium " + sc.getKNXMedium());
				
				if (groupAddressFilters.containsKey(sc))
					logger.write("", LogLevel.INFO,
							((List) groupAddressFilters.get(sc)).toArray(new GroupAddress[0])
									.toString());
				if (virtual && subnetDatapoints.containsKey(sc))
					logger.write("", LogLevel.INFO, "  "
							+ ((DatapointMap) subnetDatapoints.get(sc)).getDatapoints().toString());
			}
		}
	}

	// detect whether path of file needs to be adjusted relative to the path of the given
	// configuration file. Only applies if file resources
	private String verifyFilePath(final String configURI, final String file)
	{
		// XXX not sure if this logic is always correct
		final File f = new File(configURI);
		if (f.isFile()) {
			final File path = f.getParentFile();
			if (!new File(file).isFile())
				return new File(path, file).getAbsolutePath();
		}
		return file;
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run()
	{
		final List connectors = new ArrayList();
		final List linksToClose = new ArrayList();

		try {
			if (init(linksToClose, connectors)) {
				// create a gateway which forwards and answers most of the KNX stuff
				// if no connectors were created, gateway will throw
				gwConnectors = (SubnetConnector[]) connectors.toArray(new SubnetConnector[0]);
				gw = new KnxServerGateway("KNX server gateway", server, gwConnectors);
				if (terminal) {
					new Thread(gw, "KNX server gateway").start();
					waitForTermination();
					quit();
				}
				else
					gw.run();
			}
		}
		catch (final InterruptedException e) {
			logger.write("", LogLevel.WARN, "initialization of KNX server interrupted");
		}
		finally {
			for (final Iterator i = linksToClose.iterator(); i.hasNext();)
				((KNXNetworkLink) i.next()).close();
		}
	}

	/**
	 * Quits a running instance of the server gateway and shuts down the KNX server.
	 * <p>
	 */
	public void quit()
	{
		gw.quit();
		server.shutdown();
	}

	/**
	 * Returns the virtual links created to emulate virtual KNX subnets if requested in the
	 * configuration.
	 * <p>
	 * 
	 * @return the server virtual links as array of type KNXNetworkLink, with array length equal to
	 *         the number of virtual links (length 0 for no virtual links used)
	 */
	public KNXNetworkLink[] getVirtualLinks()
	{
		return (KNXNetworkLink[]) virtualLinks.toArray(new KNXNetworkLink[virtualLinks.size()]);
	}

	// provides the opened links as well as the created subnet connectors as list
	private boolean init(final List openLinks, final List connectors)
		throws InterruptedException
	{
		boolean failure = false;
		for (int i = 0; i < svcContainers.size(); i++) {
			final ServiceContainer sc = (ServiceContainer) svcContainers.get(i);

			KNXNetworkLink link = null;
			if (((Boolean) virtualSubnet.get(i)).booleanValue()) {
				// use network buffer to emulate KNX subnet
				final NetworkBuffer nb = NetworkBuffer.createBuffer("Virtual KNX subnet");
				final VirtualLink vl = new VirtualLink();
				virtualLinks.add(vl);
				final Configuration config = nb.addConfiguration(vl);
				config.setQueryBufferOnly(false);
				if (subnetDatapoints.containsKey(sc))
					config.setDatapointModel((DatapointModel) subnetDatapoints.get(sc));
				final StateFilter f = new StateFilter();
				config.setFilter(f, f);
				config.activate(true);
				link = config.getBufferedLink();
			}
			else {
				final String remoteHost = (String) subnetAddress.get(i);
				try {
					final int remotePort = ((Integer) subnetPort.get(i)).intValue();
					logger.write("", LogLevel.INFO, "connect to " + remoteHost + ":" + remotePort
							+ " ...");
					// can cause a delay of connection timeout in the worst case
					link = new KNXNetworkLinkIP(KNXNetworkLinkIP.TUNNELING, null,
					new InetSocketAddress(remoteHost, remotePort), false, TPSettings.TP1);
				}
				catch (final KNXException e) {
					failure = true;
					logger.write("", LogLevel.ERROR, "setup " + sc.getName() + " link to "
							+ remoteHost + ": " + e.getMessage());
				}
			}
			if (link != null) {
				server.addServiceContainer(sc);
				connectors.add(new SubnetConnector(sc, link, 1));
				openLinks.add(link);
				try {
					final InterfaceObjectServer ios = server.getInterfaceObjectServer();
					setAdditionalIndividualAddresses(ios, i + 1);
					if (groupAddressFilters.containsKey(sc))
						setGroupAddressFilter(ios, (List) groupAddressFilters.get(sc), i + 1);
				}
				catch (final KNXPropertyException e) {
					failure = true;
					logger.write("", LogLevel.ERROR, "setup " + sc.getName()
							+ " addresses in IOS: " + e.getMessage());
				}
			}
		}
		return !failure;
	}

	private void waitForTermination()
	{
		System.out.println("type 'stop' to stop the gateway and shutdown the server");
		final BufferedReader r = new BufferedReader(new InputStreamReader(System.in));
		try {
			String line;
			while ((line = r.readLine()) != null) {
				if (line.equals("stop"))
					break;
			}
			System.out.println("request to quit server");
		}
		catch (final IOException e) {}
	}

	private void readConfig(final String serverConfigURI) throws KNXMLException
	{
		final XMLReader r = XMLFactory.getInstance().createXMLReader(serverConfigURI);

		if (r.read() != XMLReader.START_TAG
				|| !r.getCurrent().getName().equals(XmlConfiguration.knxServer))
			throw new KNXMLException("no valid KNX server configuration (no "
					+ XmlConfiguration.knxServer + " element)");

		name = r.getCurrent().getAttribute(XmlConfiguration.attrName);
		friendlyName = r.getCurrent().getAttribute(XmlConfiguration.attrFriendly);

		while (r.read() != XMLReader.END_DOC) {
			final Element e = r.getCurrent();
			final String name = e.getName();
			if (r.getPosition() == XMLReader.START_TAG) {
				if (name.equals(XmlConfiguration.svcCont))
					readServiceContainer(serverConfigURI, r);
				else if (name.equals(XmlConfiguration.propDefs)) {
					r.complete(e);
					final String res = e.getAttribute(XmlConfiguration.attrId);
					if (propertyDefs != null)
						logger.write("", LogLevel.WARN, "multiple property definition "
								+ "resources (ignore " + res + ", line " + r.getLineNumber() + ")");
					else if (res != null)
						propertyDefs = res;
				}
			}
		}
	}

	private void readServiceContainer(final String configURI, final XMLReader r)
		throws KNXMLException
	{
		Element e = r.getCurrent();
		if (r.getPosition() != XMLReader.START_TAG || !e.getName().equals(XmlConfiguration.svcCont))
			throw new KNXMLException("no service container element");
		final String displayName = e.getAttribute(XmlConfiguration.attrName);
		// Boolean.parseBoolean not implemented on ME CDC
		final boolean routing = new Boolean(e.getAttribute(XmlConfiguration.attrRouting))
				.booleanValue();
		final boolean reuse = new Boolean(e.getAttribute(XmlConfiguration.attrReuseEP))
				.booleanValue();
		final boolean monitor = new Boolean(e.getAttribute(XmlConfiguration.attrMonitor))
				.booleanValue();
		final int port = Integer.parseInt(e.getAttribute(XmlConfiguration.attrUdpPort));
		final String netIf = e.getAttribute(XmlConfiguration.attrNetIf);

		String addr = "";
		int remotePort = 0;
		IndividualAddress subnet = null;
		InetAddress routingMcast = null;
		DatapointModel datapoints = null;
		boolean virtual = false;

		try {
			routingMcast = InetAddress.getByName(KNXnetIPRouting.DEFAULT_MULTICAST);
		}
		catch (final UnknownHostException ignore) {}

		while (r.read() != XMLReader.END_DOC) {
			e = r.getCurrent();
			final String name = e.getName();
			if (r.getPosition() == XMLReader.START_TAG) {
				if (name.equals(XmlConfiguration.dpRef)) {
					r.complete(e);
					final String dptsURI = verifyFilePath(configURI, e.getCharacterData());
					datapoints = new DatapointMap();
					try {
						datapoints.load(XMLFactory.getInstance().createXMLReader(dptsURI));
					}
					catch (final KNXMLException kxe) {
						datapoints = null;
						logger.write("", LogLevel.ERROR, "can not load datapoints resource "
								+ dptsURI + ": " + kxe.getMessage());
					}
				}
				else if (name.equals(XmlConfiguration.subnet)) {
					final String type = e.getAttribute(XmlConfiguration.attrType);
					final String p = e.getAttribute(XmlConfiguration.attrUdpPort);
					virtual = type.equals("virtual");
					if (type.equals("ip") && p != null)
						remotePort = Integer.parseInt(p);
					r.complete(e);
					addr = e.getCharacterData();
				}
				else if (name.equals(XmlConfiguration.grpAddrFilter))
					readGroupAddressFilter(r);
				else if (name.equals(XmlConfiguration.routingMcast)) {
					r.complete(e);
					try {
						routingMcast = InetAddress.getByName(e.getCharacterData());
					}
					catch (final UnknownHostException uhe) {
						throw new KNXMLException(uhe.getMessage(), e.getCharacterData(),
								r.getLineNumber());
					}
				}
				else {
					subnet = new IndividualAddress(r);
				}
			}
			else if (r.getPosition() == XMLReader.END_TAG) {
				if (name.equals(XmlConfiguration.svcCont)) {
					final DefaultServiceContainer sc;
					if (routing)
						sc = new RoutingServiceContainer(displayName, new HPAI((InetAddress) null,
								port), KNXMediumSettings.MEDIUM_TP1, subnet, reuse, monitor,
								routingMcast, null);
					else
						sc = new DefaultServiceContainer(displayName, new HPAI((InetAddress) null,
								port), KNXMediumSettings.MEDIUM_TP1, subnet, reuse, monitor);
					virtualSubnet.add(Boolean.valueOf(virtual));
					if (virtual && datapoints != null)
						subnetDatapoints.put(sc, datapoints);
					subnetAddress.add(addr);
					subnetPort.add(new Integer(remotePort));
					svcContainers.add(sc);
					return;
				}
			}
		}
	}

	private List readGroupAddressFilter(final XMLReader r) throws KNXMLException
	{
		assert r.getCurrent().getName().equals(XmlConfiguration.grpAddrFilter);
		assert r.getPosition() == XMLReader.START_TAG;
		r.read();
		final List list = new ArrayList();
		while (!(r.getCurrent().getName().equals(XmlConfiguration.grpAddrFilter) && r.getPosition() == XMLReader.END_TAG)) {
			list.add(new GroupAddress(r));
			r.read();
		}
		return list;
	}

	private void setGroupAddressFilter(final InterfaceObjectServer ios, final List filter,
		final int objectInstance) throws KNXPropertyException
	{
		// create byte array table
		final int size = filter.size();
		final byte[] table = new byte[size * 2];
		int idx = 0;
		for (int i = 0; i < size; i++) {
			final GroupAddress ga = (GroupAddress) filter.get(i);
			table[idx++] = (byte) (ga.getRawAddress() >> 8);
			table[idx++] = (byte) ga.getRawAddress();
		}

		if (table.length > 0) {
			// create interface object and set the address table object
			// property
			ios.addInterfaceObject(InterfaceObject.ADDRESSTABLE_OBJECT);
			ios.setProperty(InterfaceObject.ADDRESSTABLE_OBJECT, objectInstance, PID.TABLE, 1,
					size, table);
		}

		// set the handling of group addressed frames, based on whether we have set a
		// group address filter table or not
		ios.addInterfaceObject(InterfaceObject.ROUTER_OBJECT);
		// TODO explain what the available values are and set them accordingly
		final int PID_MAIN_GROUPCONFIG = 54;
		final int PID_SUB_GROUPCONFIG = 55;
		ios.setProperty(InterfaceObject.ROUTER_OBJECT, objectInstance, PID_MAIN_GROUPCONFIG, 1, 1,
				new byte[] { 0 });
		ios.setProperty(InterfaceObject.ROUTER_OBJECT, objectInstance, PID_SUB_GROUPCONFIG, 1, 1,
				new byte[] { 0 });
	}

	// set KNXnet/IP server additional individual addresses assigned to connections
	private void setAdditionalIndividualAddresses(final InterfaceObjectServer ios,
		final int objectInstance) throws KNXPropertyException
	{
		ios.setProperty(InterfaceObject.KNXNETIP_PARAMETER_OBJECT, objectInstance,
				PropertyAccess.PID.ADDITIONAL_INDIVIDUAL_ADDRESSES, 1, 1, new IndividualAddress(1,
						1, 2).toByteArray());
		ios.setProperty(InterfaceObject.KNXNETIP_PARAMETER_OBJECT, objectInstance,
				PropertyAccess.PID.ADDITIONAL_INDIVIDUAL_ADDRESSES, 2, 1, new IndividualAddress(1,
						2, 3).toByteArray());
		ios.setProperty(InterfaceObject.KNXNETIP_PARAMETER_OBJECT, objectInstance,
				PropertyAccess.PID.ADDITIONAL_INDIVIDUAL_ADDRESSES, 3, 1, new IndividualAddress(1,
						3, 4).toByteArray());
		ios.setProperty(InterfaceObject.KNXNETIP_PARAMETER_OBJECT, objectInstance,
				PropertyAccess.PID.ADDITIONAL_INDIVIDUAL_ADDRESSES, 4, 1, new IndividualAddress(1,
						3, 5).toByteArray());
		ios.setProperty(InterfaceObject.KNXNETIP_PARAMETER_OBJECT, objectInstance,
				PropertyAccess.PID.ADDITIONAL_INDIVIDUAL_ADDRESSES, 5, 1, new IndividualAddress(1,
						3, 6).toByteArray());
	}

	// A dummy link implementation used for virtual KNX networks.
	// In such network, only the Calimero network buffer is used to emulate
	// a KNX subnetwork without existing link to a real KNX installation.
	// XXX in the test network, this is public
	public class VirtualLink implements KNXNetworkLink
	{
		private final EventListeners listeners = new EventListeners();
		private final EventListeners otherListeners = new EventListeners();
		private volatile boolean closed;
		private volatile int hopCount = 6;
		private KNXMediumSettings ms = TPSettings.TP1;
		protected IndividualAddress source;

		public VirtualLink()
		{
			source = new IndividualAddress(new byte[] { 0, 0 });
		}

		// XXX in the test network, this is public
		public KNXNetworkLink getOtherLink(final IndividualAddress device)
		{
			return new VirtualLink()
			{
				{
					source = device;
				}

				/*
				 * (non-Javadoc)
				 * @see
				 * ServerMain.VirtualLink#addLinkListener(tuwien.auto.calimero.link.
				 * NetworkLinkListener)
				 */
				public void addLinkListener(final NetworkLinkListener l)
				{
					otherListeners.add(l);
				}

				/*
				 * (non-Javadoc)
				 * @see
				 * ServerMain.VirtualLink#removeLinkListener(tuwien.auto.calimero.link
				 * .NetworkLinkListener)
				 */
				public void removeLinkListener(final NetworkLinkListener l)
				{
					otherListeners.remove(l);
				}

				/**
				 * @see ServerMain.VirtualLink#send(tuwien.auto.calimero.cemi.CEMILData, boolean)
				 * @param waitForCon
				 */
				public void send(final CEMILData msg, final boolean waitForCon)
				{
					/*list.add(new Object[] { msg, otherListeners, listeners });
					synchronized (dispatcher) {
						dispatcher.notify();
					}*/
					send(msg, otherListeners, listeners);
				}
			};
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink
		 * #addLinkListener(tuwien.auto.calimero.link.event.NetworkLinkListener)
		 */
		public void addLinkListener(final NetworkLinkListener l)
		{
			listeners.add(l);
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink
		 * #removeLinkListener(tuwien.auto.calimero.link.event.NetworkLinkListener)
		 */
		public void removeLinkListener(final NetworkLinkListener l)
		{
			listeners.remove(l);
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink#setHopCount(int)
		 */
		public void setHopCount(final int count)
		{
			hopCount = count;
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink#getHopCount()
		 */
		public int getHopCount()
		{
			return hopCount;
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink
		 * #setKNXMedium(tuwien.auto.calimero.link.medium.KNXMediumSettings)
		 */
		public void setKNXMedium(final KNXMediumSettings settings)
		{
			ms = settings;
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink#getKNXMedium()
		 */
		public KNXMediumSettings getKNXMedium()
		{
			return ms;
		}

		/**
		 * @see tuwien.auto.calimero.link.KNXNetworkLink #send(tuwien.auto.calimero.cemi.CEMILData,
		 *      boolean)
		 * @param waitForCon
		 */
		public void send(final CEMILData msg, final boolean waitForCon)
		{
			send(msg, listeners, otherListeners);
		}

		private void send(final CEMILData msg, final EventListeners one, final EventListeners two)
		{
			try {
				System.out.println(DataUnitBuilder.decode(msg.getPayload(), msg.getDestination()));
				EventListener[] el = one.listeners();
				// send a .con for a .req
				if (msg.getMessageCode() == CEMILData.MC_LDATA_REQ) {
					final CEMILData f = (CEMILData) CEMIFactory.create(CEMILData.MC_LDATA_CON,
							msg.getPayload(), msg);
					final FrameEvent e = new FrameEvent(this, f);
					for (int i = 0; i < el.length; i++) {
						final NetworkLinkListener l = (NetworkLinkListener) el[i];
						l.confirmation(e);
					}
				}

				// forward .ind as is, but convert req. to .ind
				final CEMILData f = msg.getMessageCode() == CEMILData.MC_LDATA_IND ? msg
						: (CEMILData) CEMIFactory.create(CEMILData.MC_LDATA_IND, msg.getPayload(),
								msg);
				el = two.listeners();
				final FrameEvent e = new FrameEvent(this, f);
				for (int i = 0; i < el.length; i++) {
					final NetworkLinkListener l = (NetworkLinkListener) el[i];
					l.indication(e);
				}
			}
			catch (final KNXFormatException e1) {
				e1.printStackTrace();
			}
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink
		 * #sendRequest(tuwien.auto.calimero.KNXAddress, tuwien.auto.calimero.Priority,
		 * byte[])
		 */
		public void sendRequest(final KNXAddress dst, final Priority p, final byte[] nsdu)
		{
			send(new CEMILData(CEMILData.MC_LDATA_REQ, source, dst, nsdu, p), false);
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink
		 * #sendRequestWait(tuwien.auto.calimero.KNXAddress,
		 * tuwien.auto.calimero.Priority, byte[])
		 */
		public void sendRequestWait(final KNXAddress dst, final Priority p, final byte[] nsdu)
		{
			send(new CEMILData(CEMILData.MC_LDATA_REQ, source, dst, nsdu, p), true);
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink#getName()
		 */
		public String getName()
		{
			return "virtual link";
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink#isOpen()
		 */
		public boolean isOpen()
		{
			return !closed;
		}

		/*
		 * (non-Javadoc)
		 * @see tuwien.auto.calimero.link.KNXNetworkLink#close()
		 */
		public void close()
		{
			closed = true;
		}
	}
}
