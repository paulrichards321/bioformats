//
// WindowTools.java
//

/*
LOCI Plugins for ImageJ: a collection of ImageJ plugins including the
Bio-Formats Importer, Bio-Formats Exporter, Bio-Formats Macro Extensions,
Data Browser, Stack Colorizer and Stack Slicer. Copyright (C) 2005-@year@
Melissa Linkert, Curtis Rueden and Christopher Peterson.

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package loci.plugins.util;

import ij.IJ;
import ij.ImageJ;
import ij.text.TextWindow;
import ij.util.Tools;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.Frame;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Panel;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.ScrollPane;
import java.awt.Toolkit;
import java.awt.Window;
import java.io.CharArrayWriter;
import java.io.PrintWriter;

/**
 * Utility methods for managing ImageJ dialogs and windows.
 *
 * <dl><dt><b>Source code:</b></dt>
 * <dd><a href="https://skyking.microscopy.wisc.edu/trac/java/browser/trunk/components/loci-plugins/src/loci/plugins/util/WindowTools.java">Trac</a>,
 * <a href="https://skyking.microscopy.wisc.edu/svn/java/trunk/components/loci-plugins/src/loci/plugins/util/WindowTools.java">SVN</a></dd></dl>
 */
public final class WindowTools {

  // -- Constructor --

  private WindowTools() { }

  // -- Utility methods --

  /** Adds AWT scroll bars to the given container. */
  public static void addScrollBars(Container pane) {
    GridBagLayout layout = (GridBagLayout) pane.getLayout();

    // extract components
    int count = pane.getComponentCount();
    Component[] c = new Component[count];
    GridBagConstraints[] gbc = new GridBagConstraints[count];
    for (int i=0; i<count; i++) {
      c[i] = pane.getComponent(i);
      gbc[i] = layout.getConstraints(c[i]);
    }

    // clear components
    pane.removeAll();
    layout.invalidateLayout(pane);

    // create new container panel
    Panel newPane = new Panel();
    GridBagLayout newLayout = new GridBagLayout();
    newPane.setLayout(newLayout);
    for (int i=0; i<count; i++) {
      newLayout.setConstraints(c[i], gbc[i]);
      newPane.add(c[i]);
    }

    // HACK - get preferred size for container panel
    // NB: don't know a better way:
    // - newPane.getPreferredSize() doesn't work
    // - newLayout.preferredLayoutSize(newPane) doesn't work
    Frame f = new Frame();
    f.setLayout(new BorderLayout());
    f.add(newPane, BorderLayout.CENTER);
    f.pack();
    final Dimension size = newPane.getSize();
    f.remove(newPane);
    f.dispose();

    // compute best size for scrollable viewport
    size.width += 15;
    size.height += 15;
    Dimension screen = Toolkit.getDefaultToolkit().getScreenSize();
    int maxWidth = 3 * screen.width / 4;
    int maxHeight = 3 * screen.height / 4;
    if (size.width > maxWidth) size.width = maxWidth;
    if (size.height > maxHeight) size.height = maxHeight;

    // create scroll pane
    ScrollPane scroll = new ScrollPane() {
      public Dimension getPreferredSize() {
        return size;
      }
    };
    scroll.add(newPane);

    // add scroll pane to original container
    GridBagConstraints constraints = new GridBagConstraints();
    constraints.fill = GridBagConstraints.BOTH;
    constraints.weightx = 1.0;
    constraints.weighty = 1.0;
    layout.setConstraints(scroll, constraints);
    pane.add(scroll);
  }

  /**
   * Places the given window at a nice location on screen, either centered
   * below the ImageJ window if there is one, or else centered on screen.
   */
  public static void placeWindow(Window w) {
    Dimension size = w.getSize();

    Dimension screen = Toolkit.getDefaultToolkit().getScreenSize();

    ImageJ ij = IJ.getInstance();

    Point p = new Point();

    if (ij == null) {
      // center config window on screen
      p.x = (screen.width - size.width) / 2;
      p.y = (screen.height - size.height) / 2;
    }
    else {
      // place config window below ImageJ window
      Rectangle ijBounds = ij.getBounds();
      p.x = ijBounds.x + (ijBounds.width - size.width) / 2;
      p.y = ijBounds.y + ijBounds.height + 5;
    }

    // nudge config window away from screen edges
    final int pad = 10;
    if (p.x < pad) p.x = pad;
    else if (p.x + size.width + pad > screen.width) {
      p.x = screen.width - size.width - pad;
    }
    if (p.y < pad) p.y = pad;
    else if (p.y + size.height + pad > screen.height) {
      p.y = screen.height - size.height - pad;
    }

    w.setLocation(p);
  }

  /** Reports an exception in an ImageJ text window. */
  public static void reportException(Throwable t) {
    // stolen from IJ.Executor.run()
    IJ.showStatus("");
    IJ.showProgress(1.0);
    CharArrayWriter caw = new CharArrayWriter();
    PrintWriter pw = new PrintWriter(caw);
    t.printStackTrace(pw);
    String s = caw.toString();
    if (IJ.isMacintosh()) {
      if (s.indexOf("ThreadDeath") > 0) return;
      s = Tools.fixNewLines(s);
    }
    if (IJ.getInstance() != null) new TextWindow("Exception", s, 350, 250);
    else IJ.log(s);
  }

}