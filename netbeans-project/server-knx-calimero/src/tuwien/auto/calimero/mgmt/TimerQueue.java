/*
    Calimero 2 - A library for KNX network access
    Copyright (c) 2011, 2012 B. Malinowsky

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

package tuwien.auto.calimero.mgmt;

import java.util.ArrayList;
import java.util.List;

import tuwien.auto.calimero.exception.KNXIllegalArgumentException;


/**
 * A timer queue, which allows to submit timeouts and getting notified when that time span
 * has passed.
 * <p>
 * Its main purpose is to avoid a standard threaded destination timeout mechanism, which
 * gets a resource hog with respect to threads in KNX address scanning management
 * procedures. It uses a single thread approach to wait for the next submitted timeout to
 * pass, and invokes the corresponding notifiable for that timeout.<br>
 * The reason this class exists here is that we cannot depend on built-in functionality on
 * J2ME platforms deployed on resource-constrained devices.<br>
 * <p>
 * Implementation note: a newly submitted notifiable is always assumed to time out after
 * any previous submitted notifiable.
 * 
 * @author B. Malinowsky
 */
final class TimerQueue extends Thread
{
	// synchronize on notifiables as monitor for both notifiables and endTimes lists
	private final List notifiables = new ArrayList();
	private final List endTimes = new ArrayList();
	
	public TimerQueue()
	{
		super("TimerQueue");
		setDaemon(true);
	}

	/* (non-Javadoc)
	 * @see java.lang.Thread#run()
	 */
	public void run()
	{
		try {
			while (true) {
				Runnable notify = null;
				synchronized (notifiables) {
					if (notifiables.isEmpty()) {
						// nothing to do
						notifiables.wait();
					}
					else {
						final Runnable next = (Runnable) notifiables.get(0);
						final Long end = (Long) endTimes.get(0);
						long remaining = end.longValue() - System.currentTimeMillis();
						if (remaining > 0) {
							notifiables.wait(remaining);
							remaining = end.longValue() - System.currentTimeMillis();
						}
						// in addition to timed-out wait, we have to check whether the
						// last endTime was shifted by canceling or another submit
						// immediately before. Using == for end time comparison ensures
						// we have the correct entry, and not a subsequent submission
						// using the same notifiable
						if (remaining <= 0 && !notifiables.isEmpty()
							&& notifiables.get(0) == next && endTimes.get(0) == end) {
							notifiables.remove(0);
							endTimes.remove(0);
							notify = next;
						}
					}
				}
				// invoke notifiable outside synchronized block, as a notifiable might destroy
				// and remove itself from the timer queue
				try {
					if (notify != null)
						notify.run();
				}
				catch (final RuntimeException e) {
					// can't do a lot here
					e.printStackTrace();
				}
			}
		}
		catch (final InterruptedException e) {
			System.err.println("TimerQueue stopped, still submitted = " + notifiables.size());
		}
	}

	// this will remove the first notifiable entry, comparison by reference
	void cancel(final Runnable notifiable)
	{
		synchronized (notifiables) {
			final int index = notifiables.indexOf(notifiable);
			if (index == -1)
				return;
			notifiables.remove(index);
			endTimes.remove(index);
			notifiables.notify();
		}
	}

	void submit(final Runnable notifiable, final long endTime)
	{
		if (endTime <= 0 || notifiable == null)
			throw new KNXIllegalArgumentException("submit to timer queue");
		// we assume here the submitted end time is later than last entry in list
		// TODO change this if we find out we have greatly varying time-outs
		synchronized (notifiables) {
			notifiables.add(notifiable);
			endTimes.add(new Long(endTime));
			notifiables.notify();
		}
	}
	
	void quit()
	{
		interrupt();
	}
}
