/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerHeight;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerWidth;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerX;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerY;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AntiAlias;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AutoVisualize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreGranularity;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreMinimization;
import static edu.mit.csail.sdg.alloy4.A4Preferences.FontName;
import static edu.mit.csail.sdg.alloy4.A4Preferences.FontSize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.ImplicitThis;
import static edu.mit.csail.sdg.alloy4.A4Preferences.InferPartialInstance;
import static edu.mit.csail.sdg.alloy4.A4Preferences.LAF;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model0;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model1;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model2;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model3;
import static edu.mit.csail.sdg.alloy4.A4Preferences.NoOverflow;
import static edu.mit.csail.sdg.alloy4.A4Preferences.RecordKodkod;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SkolemDepth;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Solver;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubMemory;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubStack;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SyntaxDisabled;
import static edu.mit.csail.sdg.alloy4.A4Preferences.TabSize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Unrolls;
import static edu.mit.csail.sdg.alloy4.A4Preferences.VerbosityPref;
import static edu.mit.csail.sdg.alloy4.A4Preferences.WarningNonfatal;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Welcome;
import static edu.mit.csail.sdg.alloy4.OurUtil.menu;
import static edu.mit.csail.sdg.alloy4.OurUtil.menuItem;
import static edu.mit.csail.sdg.ast.ExprUnary.Op.SOMEOF;
import static edu.mit.csail.sdg.ast.Sig.UNIV;
import static java.awt.event.InputEvent.getMaskForButton;
import static java.awt.event.KeyEvent.VK_A;
import static java.awt.event.KeyEvent.VK_ALT;
import static java.awt.event.KeyEvent.VK_E;
import static java.awt.event.KeyEvent.VK_PAGE_DOWN;
import static java.awt.event.KeyEvent.VK_PAGE_UP;
import static java.awt.event.KeyEvent.VK_SHIFT;

import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.lang.reflect.Method;
import java.util.*;
import java.util.List;

import javax.swing.*;
import javax.swing.Timer;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;
import javax.swing.event.*;
import javax.swing.plaf.FontUIResource;
import javax.swing.text.html.HTMLDocument;

import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.printExpr.*;
import edu.mit.csail.sdg.translator.*;
import org.alloytools.alloy.core.AlloyCore;

//import com.apple.eawt.Application;
//import com.apple.eawt.ApplicationAdapter;
//import com.apple.eawt.ApplicationEvent;
//

import edu.mit.csail.sdg.alloy4.A4Preferences.BooleanPref;
import edu.mit.csail.sdg.alloy4.A4Preferences.ChoicePref;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.alloy4.A4Preferences.StringPref;
import edu.mit.csail.sdg.alloy4.A4Preferences.Verbosity;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.alloy4whole.SimpleReporter.SimpleCallback1;
import edu.mit.csail.sdg.alloy4whole.SimpleReporter.SimpleTask1;
import edu.mit.csail.sdg.alloy4whole.SimpleReporter.SimpleTask2;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.sim.SimInstance;
import edu.mit.csail.sdg.sim.SimTuple;
import edu.mit.csail.sdg.sim.SimTupleset;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import kodkod.engine.fol2sat.HigherOrderDeclException;

/**
 * Simple graphical interface for accessing various features of the analyzer.
 * <p>
 * Except noted below, methods in this class can only be called by the AWT event
 * thread.
 * <p>
 * The methods that might get called from other threads are: <br>
 * (1) the run() method in SatRunner is launched from a fresh thread <br>
 * (2) the run() method in the instance watcher (in constructor) is launched
 * from a fresh thread
 */
public final class SimpleGUI implements ComponentListener, Listener {

    MacUtil macUtil;

    /**
     * The latest welcome screen; each time we update the welcome screen, we
     * increment this number.
     */
    // private static final int welcomeLevel = 2;

    // Verify that the graphics environment is set up
    static {
        try {
            GraphicsEnvironment.getLocalGraphicsEnvironment();
        } catch (Throwable ex) {
            System.err.println("Unable to start the graphical environment.");
            System.err.println("If you're on Mac OS X:");
            System.err.println("   Please make sure you are running as the current local user.");
            System.err.println("If you're on Linux or FreeBSD:");
            System.err.println("   Please make sure your X Windows is configured.");
            System.err.println("   You can verify this by typing \"xhost\"; it should not give an error message.");
            System.err.flush();
            System.exit(1);
        }
    }

    /** The JFrame for the main window. */
    private JFrame                frame;

    /** The JFrame for the visualizer window. */
    private VizGUI                viz;

    /**
     * The "File", "Edit", "Run", "Option", "Window", and "Help" menus.
     */
    //colorful merge
    private JMenu                 filemenu, editmenu, runmenu, optmenu, windowmenu, windowmenu2, helpmenu,mergemenu;

    /** The toolbar. */
    private JToolBar              toolbar;

    /** The various toolbar buttons. */
    private JButton               runbutton, stopbutton, showbutton;

    /** The Splitpane. */
    private JSplitPane            splitpane;

    /**
     * The JLabel that displays the current line/column position, etc.
     */
    private JLabel                status;

    /**
     * Whether the editor has the focus, or the log window has the focus.
     */
    private boolean               lastFocusIsOnEditor    = true;

    /** The text editor. */
    private OurTabbedSyntaxWidget text;

    /** The "message panel" on the right. */
    private SwingLogPanel         log;

    /** The scrollpane containing the "message panel". */
    private JScrollPane           logpane;

    /** The last "find" that the user issued. */
    private String                lastFind               = "";

    /** The last find is case-sensitive or not. */
    private boolean               lastFindCaseSensitive  = true;

    /** The last find is forward or not. */
    private boolean               lastFindForward        = true;

    /** The icon for a "checked" menu item. */
    private static final Icon     iconYes                = OurUtil.loadIcon("images/menu1.gif");

    /** The icon for an "unchecked" menu item. */
    private static final Icon     iconNo                 = OurUtil.loadIcon("images/menu0.gif");

    /**
     * The system-specific file separator (forward-slash on UNIX, back-slash on
     * Windows, etc.)
     */
    private static final String   fs                     = System.getProperty("file.separator");

    /**
     * The darker background color (for the MessageLog window and the Toolbar and
     * the Status Bar, etc.)
     */
    private static final Color    background             = new Color(0.9f, 0.9f, 0.9f);

    /**
     * If subrunning==true: 0 means SAT solving; 1 means metamodel; 2 means
     * enumeration.
     */
    private int                   subrunningTask         = 0;

    /**
     * The amount of memory (in MB) currently allocated for this.subprocess
     */
    private int                   subMemoryNow           = 0;

    /**
     * The amount of stack (in KB) currently allocated for this.subprocess
     */
    private int                   subStackNow            = 0;

    /**
     * The list of commands (this field will be cleared to null when the text buffer
     * is edited).
     */
    private List<Command>         commands               = null;
    //colorful merge
    private  Map<String,Map<Map<Integer,Pos>,Sig>>       sigs               = null;

    /** The latest executed command. */
    private int                   latestCommand          = 0;

    /**
     * The most recent Alloy version (as queried from alloy.mit.edu); -1 if
     * alloy.mit.edu has not replied yet.
     */
    private int                   latestAlloyVersion     = (-1);

    /**
     * The most recent Alloy version name (as queried from alloy.mit.edu); "unknown"
     * if alloy.mit.edu has not replied yet.
     */
    private String                latestAlloyVersionName = "unknown";

    /**
     * If it's not "", then it is the XML filename for the latest satisfying
     * instance or the latest metamodel.
     */
    private String                latestInstance         = "";

    /**
     * If it's not "", then it is the latest instance or metamodel during the most
     * recent click of "Execute".
     */
    private String                latestAutoInstance     = "";

    /**
     * If true, that means the event handlers should return a Runner encapsulating
     * them, rather than perform the actual work.
     */
    private boolean               wrap                   = false;

    /** The preferences dialog. */
    private PreferencesDialog     prefDialog;

    // ====== helper methods =================================================//

    /**
     * Inserts "filename" into the "recently opened file list".
     */
    private void addHistory(String filename) {
        String name0 = Model0.get(), name1 = Model1.get(), name2 = Model2.get();
        if (name0.equals(filename))
            return;
        else {
            Model0.set(filename);
            Model1.set(name0);
        }
        if (name1.equals(filename))
            return;
        else
            Model2.set(name1);
        if (name2.equals(filename))
            return;
        else
            Model3.set(name2);
    }

    /** Sets the flag "lastFocusIsOnEditor" to be true. */
    private Runner notifyFocusGained() {
        if (wrap)
            return wrapMe();
        lastFocusIsOnEditor = true;
        return null;
    }

    /** Sets the flag "lastFocusIsOnEditor" to be false. */
    void notifyFocusLost() {
        lastFocusIsOnEditor = false;
    }

    /** Updates the status bar at the bottom of the screen. */
    private Runner notifyChange() {
        if (wrap)
            return wrapMe();
        commands = null;
        //colorful merge
        sigs=null;
        if (text == null)
            return null; // If this was called prior to the "text" being fully
                        // initialized
        OurSyntaxWidget t = text.get();
        if (Util.onMac())
            frame.getRootPane().putClientProperty("windowModified", Boolean.valueOf(t.modified()));
        if (t.isFile())
            frame.setTitle(t.getFilename());
        else
            frame.setTitle("Alloy Analyzer " + Version.version());
        toolbar.setBorder(new OurBorder(false, false, text.count() <= 1, false));
        int c = t.getCaret();
        int y = t.getLineOfOffset(c) + 1;
        int x = c - t.getLineStartOffset(y - 1) + 1;
        status.setText("<html>&nbsp; Line " + y + ", Column " + x + (t.modified() ? " <b style=\"color:#B43333;\">[modified]</b></html>" : "</html>"));
        return null;
    }

    /**
     * Helper method that returns a hopefully very short name for a file name.
     */
    public static String slightlyShorterFilename(String name) {
        if (name.toLowerCase(Locale.US).endsWith(".als")) {
            int i = name.lastIndexOf('/');
            if (i >= 0)
                name = name.substring(i + 1);
            i = name.lastIndexOf('\\');
            if (i >= 0)
                name = name.substring(i + 1);
            return name.substring(0, name.length() - 4);
        } else if (name.toLowerCase(Locale.US).endsWith(".xml")) {
            int i = name.lastIndexOf('/');
            if (i > 0)
                i = name.lastIndexOf('/', i - 1);
            if (i >= 0)
                name = name.substring(i + 1);
            i = name.lastIndexOf('\\');
            if (i > 0)
                i = name.lastIndexOf('\\', i - 1);
            if (i >= 0)
                name = name.substring(i + 1);
            return name.substring(0, name.length() - 4);
        }
        return name;
    }

    /**
     * Copy the required files from the JAR into a temporary directory.
     */
    private void copyFromJAR() {
        // Compute the appropriate platform
        String os = System.getProperty("os.name").toLowerCase(Locale.US).replace(' ', '-');
        if (os.startsWith("mac-"))
            os = "mac";
        else if (os.startsWith("windows-"))
            os = "windows";
        String arch = System.getProperty("os.arch").toLowerCase(Locale.US).replace(' ', '-');
        if (arch.equals("powerpc"))
            arch = "ppc-" + os;
        else
            arch = arch.replaceAll("\\Ai[3456]86\\z", "x86") + "-" + os;
        if (os.equals("mac"))
            arch = "x86-mac"; // our pre-compiled binaries are all universal
                             // binaries
                             // Find out the appropriate Alloy directory
        final String platformBinary = alloyHome() + fs + "binary";
        // Write a few test files
        try {
            (new File(platformBinary)).mkdirs();
            Util.writeAll(platformBinary + fs + "tmp.cnf", "p cnf 3 1\n1 0\n");
        } catch (Err er) {
            // The error will be caught later by the "berkmin" or "spear" test
        }
        // Copy the platform-dependent binaries
        Util.copy(true, false, platformBinary, arch + "/libminisat.so", arch + "/libminisatx1.so", arch + "/libminisat.jnilib", arch + "/libminisat.dylib", arch + "/libminisatprover.so", arch + "/libminisatproverx1.so", arch + "/libminisatprover.jnilib", arch + "/libminisatprover.dylib", arch + "/libzchaff.so", arch + "/libzchaffmincost.so", arch + "/libzchaffx1.so", arch + "/libzchaff.jnilib", arch + "/liblingeling.so", arch + "/liblingeling.dylib", arch + "/liblingeling.jnilib", arch + "/plingeling", arch + "/libglucose.so", arch + "/libglucose.dylib", arch + "/libglucose.jnilib", arch + "/libcryptominisat.so", arch + "/libcryptominisat.la", arch + "/libcryptominisat.dylib", arch + "/libcryptominisat.jnilib", arch + "/berkmin", arch + "/spear", arch + "/cryptominisat");
        Util.copy(false, false, platformBinary, arch + "/minisat.dll", arch + "/cygminisat.dll", arch + "/libminisat.dll.a", arch + "/minisatprover.dll", arch + "/cygminisatprover.dll", arch + "/libminisatprover.dll.a", arch + "/glucose.dll", arch + "/cygglucose.dll", arch + "/libglucose.dll.a", arch + "/zchaff.dll", arch + "/berkmin.exe", arch + "/spear.exe");
        // Copy the model files
        Util.copy(false, true, alloyHome(), "models/book/appendixA/addressBook1.als", "models/book/appendixA/addressBook2.als", "models/book/appendixA/barbers.als", "models/book/appendixA/closure.als", "models/book/appendixA/distribution.als", "models/book/appendixA/phones.als", "models/book/appendixA/prison.als", "models/book/appendixA/properties.als", "models/book/appendixA/ring.als", "models/book/appendixA/spanning.als", "models/book/appendixA/tree.als", "models/book/appendixA/tube.als", "models/book/appendixA/undirected.als", "models/book/appendixE/hotel.thm", "models/book/appendixE/p300-hotel.als", "models/book/appendixE/p303-hotel.als", "models/book/appendixE/p306-hotel.als", "models/book/chapter2/addressBook1a.als", "models/book/chapter2/addressBook1b.als", "models/book/chapter2/addressBook1c.als", "models/book/chapter2/addressBook1d.als", "models/book/chapter2/addressBook1e.als", "models/book/chapter2/addressBook1f.als", "models/book/chapter2/addressBook1g.als", "models/book/chapter2/addressBook1h.als", "models/book/chapter2/addressBook2a.als", "models/book/chapter2/addressBook2b.als", "models/book/chapter2/addressBook2c.als", "models/book/chapter2/addressBook2d.als", "models/book/chapter2/addressBook2e.als", "models/book/chapter2/addressBook3a.als", "models/book/chapter2/addressBook3b.als", "models/book/chapter2/addressBook3c.als", "models/book/chapter2/addressBook3d.als", "models/book/chapter2/theme.thm", "models/book/chapter4/filesystem.als", "models/book/chapter4/grandpa1.als", "models/book/chapter4/grandpa2.als", "models/book/chapter4/grandpa3.als", "models/book/chapter4/lights.als", "models/book/chapter5/addressBook.als", "models/book/chapter5/lists.als", "models/book/chapter5/sets1.als", "models/book/chapter5/sets2.als", "models/book/chapter6/hotel.thm", "models/book/chapter6/hotel1.als", "models/book/chapter6/hotel2.als", "models/book/chapter6/hotel3.als", "models/book/chapter6/hotel4.als", "models/book/chapter6/mediaAssets.als", "models/book/chapter6/memory/abstractMemory.als", "models/book/chapter6/memory/cacheMemory.als", "models/book/chapter6/memory/checkCache.als", "models/book/chapter6/memory/checkFixedSize.als", "models/book/chapter6/memory/fixedSizeMemory.als", "models/book/chapter6/memory/fixedSizeMemory_H.als", "models/book/chapter6/ringElection.thm", "models/book/chapter6/ringElection1.als", "models/book/chapter6/ringElection2.als", "models/examples/algorithms/dijkstra.als", "models/examples/algorithms/dijkstra.thm", "models/examples/algorithms/messaging.als", "models/examples/algorithms/messaging.thm", "models/examples/algorithms/opt_spantree.als", "models/examples/algorithms/opt_spantree.thm", "models/examples/algorithms/peterson.als", "models/examples/algorithms/ringlead.als", "models/examples/algorithms/ringlead.thm", "models/examples/algorithms/s_ringlead.als", "models/examples/algorithms/stable_mutex_ring.als", "models/examples/algorithms/stable_mutex_ring.thm", "models/examples/algorithms/stable_orient_ring.als", "models/examples/algorithms/stable_orient_ring.thm", "models/examples/algorithms/stable_ringlead.als", "models/examples/algorithms/stable_ringlead.thm", "models/examples/case_studies/INSLabel.als", "models/examples/case_studies/chord.als", "models/examples/case_studies/chord2.als", "models/examples/case_studies/chordbugmodel.als", "models/examples/case_studies/com.als", "models/examples/case_studies/firewire.als", "models/examples/case_studies/firewire.thm", "models/examples/case_studies/ins.als", "models/examples/case_studies/iolus.als", "models/examples/case_studies/sync.als", "models/examples/case_studies/syncimpl.als", "models/examples/puzzles/farmer.als", "models/examples/puzzles/farmer.thm", "models/examples/puzzles/handshake.als", "models/examples/puzzles/handshake.thm", "models/examples/puzzles/hanoi.als", "models/examples/puzzles/hanoi.thm", "models/examples/systems/file_system.als", "models/examples/systems/file_system.thm", "models/examples/systems/javatypes_soundness.als", "models/examples/systems/lists.als", "models/examples/systems/lists.thm", "models/examples/systems/marksweepgc.als", "models/examples/systems/views.als", "models/examples/toys/birthday.als", "models/examples/toys/birthday.thm", "models/examples/toys/ceilingsAndFloors.als", "models/examples/toys/ceilingsAndFloors.thm", "models/examples/toys/genealogy.als", "models/examples/toys/genealogy.thm", "models/examples/toys/grandpa.als", "models/examples/toys/grandpa.thm", "models/examples/toys/javatypes.als", "models/examples/toys/life.als", "models/examples/toys/life.thm", "models/examples/toys/numbering.als", "models/examples/toys/railway.als", "models/examples/toys/railway.thm", "models/examples/toys/trivial.als", "models/examples/tutorial/farmer.als", "models/util/boolean.als", "models/util/graph.als", "models/util/integer.als", "models/util/natural.als", "models/util/ordering.als", "models/util/relation.als", "models/util/seqrel.als", "models/util/sequence.als", "models/util/sequniv.als", "models/util/ternary.als", "models/util/time.als");
        // Record the locations
        System.setProperty("alloy.theme0", alloyHome() + fs + "models");
        System.setProperty("alloy.home", alloyHome());
    }

    /** Called when this window is resized. */
    @Override
    public void componentResized(ComponentEvent e) {
        componentMoved(e);
    }

    /** Called when this window is moved. */
    @Override
    public void componentMoved(ComponentEvent e) {
        AnalyzerWidth.set(frame.getWidth());
        AnalyzerHeight.set(frame.getHeight());
        AnalyzerX.set(frame.getX());
        AnalyzerY.set(frame.getY());
    }

    /** Called when this window is shown. */
    @Override
    public void componentShown(ComponentEvent e) {}

    /** Called when this window is hidden. */
    @Override
    public void componentHidden(ComponentEvent e) {}

    /**
     * Wraps the calling method into a Runnable whose run() will call the calling
     * method with (false) as the only argument.
     */
    private Runner wrapMe() {
        final String name;
        try {
            throw new Exception();
        } catch (Exception ex) {
            name = ex.getStackTrace()[1].getMethodName();
        }
        Method[] methods = getClass().getDeclaredMethods();
        Method m = null;
        for (int i = 0; i < methods.length; i++)
            if (methods[i].getName().equals(name)) {
                m = methods[i];
                break;
            }
        final Method method = m;
        return new Runner() {

            private static final long serialVersionUID = 0;

            @Override
            public void run() {
                try {
                    method.setAccessible(true);
                    method.invoke(SimpleGUI.this, new Object[] {});
                } catch (Throwable ex) {
                    ex = new IllegalArgumentException("Failed call to " + name + "()", ex);
                    Thread.getDefaultUncaughtExceptionHandler().uncaughtException(Thread.currentThread(), ex);
                }
            }

            @Override
            public void run(Object arg) {
                run();
            }
        };
    }

    /**
     * Wraps the calling method into a Runnable whose run() will call the calling
     * method with (false,argument) as the two arguments.
     */
    private Runner wrapMe(final Object argument) {
        final String name;
        try {
            throw new Exception();
        } catch (Exception ex) {
            name = ex.getStackTrace()[1].getMethodName();
        }
        Method[] methods = getClass().getDeclaredMethods();
        Method m = null;
        for (int i = 0; i < methods.length; i++)
            if (methods[i].getName().equals(name)) {
                m = methods[i];
                break;
            }
        final Method method = m;
        return new Runner() {

            private static final long serialVersionUID = 0;

            @Override
            public void run(Object arg) {
                try {
                    method.setAccessible(true);
                    method.invoke(SimpleGUI.this, new Object[] {
                                                                arg
                    });
                } catch (Throwable ex) {
                    ex = new IllegalArgumentException("Failed call to " + name + "(" + arg + ")", ex);
                    Thread.getDefaultUncaughtExceptionHandler().uncaughtException(Thread.currentThread(), ex);
                }
            }

            @Override
            public void run() {
                run(argument);
            }
        };
    }

    /**
     * This variable caches the result of alloyHome() function call.
     */
    private static String alloyHome = null;

    /**
     * Find a temporary directory to store Alloy files; it's guaranteed to be a
     * canonical absolute path.
     */
    private static synchronized String alloyHome() {
        if (alloyHome != null)
            return alloyHome;
        String temp = System.getProperty("java.io.tmpdir");
        if (temp == null || temp.length() == 0)
            OurDialog.fatal("Error. JVM need to specify a temporary directory using java.io.tmpdir property.");
        String username = System.getProperty("user.name");
        File tempfile = new File(temp + File.separatorChar + "alloy4tmp40-" + (username == null ? "" : username));
        tempfile.mkdirs();
        String ans = Util.canon(tempfile.getPath());
        if (!tempfile.isDirectory()) {
            OurDialog.fatal("Error. Cannot create the temporary directory " + ans);
        }
        if (!Util.onWindows()) {
            String[] args = {
                             "chmod", "700", ans
            };
            try {
                Runtime.getRuntime().exec(args).waitFor();
            } catch (Throwable ex) {} // We only intend to make a best effort.
        }
        return alloyHome = ans;
    }

    /**
     * Create an empty temporary directory for use, designate it "deleteOnExit",
     * then return it. It is guaranteed to be a canonical absolute path.
     */
    private static String maketemp() {
        Random r = new Random(new Date().getTime());
        while (true) {
            int i = r.nextInt(1000000);
            String dest = alloyHome() + File.separatorChar + "tmp" + File.separatorChar + i;
            File f = new File(dest);
            if (f.mkdirs()) {
                f.deleteOnExit();
                return Util.canon(dest);
            }
        }
    }

    /**
     * Return the number of bytes used by the Temporary Directory (or return -1 if
     * the answer exceeds "long")
     */
    private static long computeTemporarySpaceUsed() {
        long ans = iterateTemp(null, false);
        if (ans < 0)
            return -1;
        else
            return ans;
    }

    /** Delete every file in the Temporary Directory. */
    private static void clearTemporarySpace() {
        iterateTemp(null, true);
        // Also clear the temp dir from previous versions of Alloy4
        String temp = System.getProperty("java.io.tmpdir");
        if (temp == null || temp.length() == 0)
            return;
        String username = System.getProperty("user.name");
        if (username == null)
            username = "";
        for (int i = 1; i < 40; i++)
            iterateTemp(temp + File.separatorChar + "alloy4tmp" + i + "-" + username, true);
    }

    /**
     * Helper method for performing either computeTemporarySpaceUsed() or
     * clearTemporarySpace()
     */
    private static long iterateTemp(String filename, boolean delete) {
        long ans = 0;
        if (filename == null)
            filename = alloyHome() + File.separatorChar + "tmp";
        File x = new File(filename);
        if (x.isDirectory()) {
            for (String subfile : x.list()) {
                long tmp = iterateTemp(filename + File.separatorChar + subfile, delete);
                if (ans >= 0)
                    ans = ans + tmp;
            }
        } else if (x.isFile()) {
            long tmp = x.length();
            if (ans >= 0)
                ans = ans + tmp;
        }
        if (delete)
            x.delete();
        return ans;
    }

    // ===============================================================================================================//

    /** This method refreshes the "file" menu. */
    private Runner doRefreshFile() {
        if (wrap)
            return wrapMe();
        try {
            wrap = true;
            filemenu.removeAll();
            menuItem(filemenu, "New", 'N', 'N', doNew());
            menuItem(filemenu, "Open...", 'O', 'O', doOpen());
            if (!Util.onMac())
                menuItem(filemenu, "Open Sample Models...", VK_ALT, 'O', doBuiltin());
            else
                menuItem(filemenu, "Open Sample Models...", doBuiltin());
            JMenu recentmenu;
            filemenu.add(recentmenu = new JMenu("Open Recent"));
            menuItem(filemenu, "Reload all", 'R', 'R', doReloadAll());
            menuItem(filemenu, "Save", 'S', 'S', doSave());
            if (Util.onMac())
                menuItem(filemenu, "Save As...", VK_SHIFT, 'S', doSaveAs());
            else
                menuItem(filemenu, "Save As...", 'A', doSaveAs());
            menuItem(filemenu, "Close", 'W', 'W', doClose());
            menuItem(filemenu, "Clear Temporary Directory", doClearTemp());
            menuItem(filemenu, "Quit", 'Q', (Util.onMac() ? -1 : 'Q'), doQuit());
            boolean found = false;
            for (StringPref p : new StringPref[] {
                                                  Model0, Model1, Model2, Model3
            }) {
                String name = p.get();
                if (name.length() > 0) {
                    found = true;
                    menuItem(recentmenu, name, doOpenFile(name));
                }
            }
            recentmenu.addSeparator();
            menuItem(recentmenu, "Clear Menu", doClearRecent());
            recentmenu.setEnabled(found);
        } finally {
            wrap = false;
        }
        return null;
    }




    /** This method performs File->New. */
    private Runner doNew() {
        if (!wrap) {
            text.newtab(null);
            notifyChange();
            doShow();
        }
        return wrapMe();
    }

    /** This method performs File->Open. */
    private Runner doOpen() {
        if (wrap)
            return wrapMe();
        File file = getFile(null);
        if (file != null) {
            Util.setCurrentDirectory(file.getParentFile());
            doOpenFile(file.getPath());
        }
        return null;
    }

    /** This method performs File->OpenBuiltinModels. */
    private Runner doBuiltin() {
        if (wrap)
            return wrapMe();
        File file = getFile(alloyHome() + fs + "models");
        if (file != null) {
            doOpenFile(file.getPath());
        }
        return null;
    }

    private File getFile(String home) {
        File file = OurDialog.askFile(true, home, new String[] {
                                                                ".als", ".md", "*"
        }, "Alloy (.als) or Markdown (.md) files");
        return file;
    }

    /** This method performs File->ReloadAll. */
    private Runner doReloadAll() {
        if (!wrap)
            text.reloadAll();
        return wrapMe();
    }

    /** This method performs File->ClearRecentFiles. */
    private Runner doClearRecent() {
        if (!wrap) {
            Model0.set("");
            Model1.set("");
            Model2.set("");
            Model3.set("");
        }
        return wrapMe();
    }

    /** This method performs File->Save. */
    private Runner doSave() {
        if (!wrap) {
            String ans = text.save(false);
            if (ans == null)
                return null;
            notifyChange();
            addHistory(ans);
            log.clearError();
        }
        return wrapMe();
    }

    /** This method performs File->SaveAs. */
    private Runner doSaveAs() {
        if (!wrap) {
            String ans = text.save(true);
            if (ans == null)
                return null;
            notifyChange();
            addHistory(ans);
            log.clearError();
        }
        return wrapMe();
    }

    /**
     * This method clears the temporary files and then reinitialize the temporary
     * directory.
     */
    private Runner doClearTemp() {
        if (!wrap) {
            clearTemporarySpace();
            copyFromJAR();
            log.logBold("Temporary directory has been cleared.\n\n");
            log.logDivider();
            log.flush();
        }
        return wrapMe();
    }

    /** This method performs File->Close. */
    private Runner doClose() {
        if (!wrap)
            text.close();
        return wrapMe();
    }

    /** This method performs File->Quit. */
    public Runner doQuit() {
        if (!wrap)
            if (text.closeAll()) {
                try {
                    WorkerEngine.stop();
                } finally {
                    System.exit(0);
                }
            }
        return wrapMe();
    }

    // ===============================================================================================================//

    /** This method refreshes the "edit" menu. */
    private Runner doRefreshEdit() {
        if (wrap)
            return wrapMe();
        try {
            wrap = true;
            boolean canUndo = text.get().canUndo();
            boolean canRedo = text.get().canRedo();
            editmenu.removeAll();
            menuItem(editmenu, "Undo", 'Z', 'Z', doUndo(), canUndo);
            if (Util.onMac())
                menuItem(editmenu, "Redo", VK_SHIFT, 'Z', doRedo(), canRedo);
            else
                menuItem(editmenu, "Redo", 'Y', 'Y', doRedo(), canRedo);
            editmenu.addSeparator();
            menuItem(editmenu, "Cut", 'X', 'X', doCut());
            menuItem(editmenu, "Copy", 'C', 'C', doCopy());
            menuItem(editmenu, "Paste", 'V', 'V', doPaste());
            editmenu.addSeparator();
            menuItem(editmenu, "Go To...", 'T', 'T', doGoto());
            menuItem(editmenu, "Previous File", VK_PAGE_UP, VK_PAGE_UP, doGotoPrevFile(), text.count() > 1);
            menuItem(editmenu, "Next File", VK_PAGE_DOWN, VK_PAGE_DOWN, doGotoNextFile(), text.count() > 1);
            editmenu.addSeparator();
            menuItem(editmenu, "Find...", 'F', 'F', doFind());
            menuItem(editmenu, "Find Next", 'G', 'G', doFindNext());
            editmenu.addSeparator();
            if (!Util.onMac())
                menuItem(editmenu, "Preferences", 'P', 'P', doPreferences());
        } finally {
            wrap = false;
        }
        return null;
    }

    /** This method performs Edit->Undo. */
    private Runner doUndo() {
        if (!wrap)
            text.get().undo();
        return wrapMe();
    }

    /** This method performs Edit->Redo. */
    private Runner doRedo() {
        if (!wrap)
            text.get().redo();
        return wrapMe();
    }

    /** This method performs Edit->Copy. */
    private Runner doCopy() {
        if (!wrap) {
            if (lastFocusIsOnEditor)
                text.get().copy();
            else
                log.copy();
        }
        return wrapMe();
    }

    /** This method performs Edit->Cut. */
    private Runner doCut() {
        if (!wrap && lastFocusIsOnEditor)
            text.get().cut();
        return wrapMe();
    }

    /** This method performs Edit->Paste. */
    private Runner doPaste() {
        if (!wrap && lastFocusIsOnEditor)
            text.get().paste();
        return wrapMe();
    }

    /** This method performs Edit->Find. */
    private Runner doFind() {
        if (wrap)
            return wrapMe();
        JTextField x = OurUtil.textfield(lastFind, 30);
        x.selectAll();
        JCheckBox c = new JCheckBox("Case Sensitive?", lastFindCaseSensitive);
        c.setMnemonic('c');
        JCheckBox b = new JCheckBox("Search Backward?", !lastFindForward);
        b.setMnemonic('b');
        if (!OurDialog.getInput("Find", "Text:", x, " ", c, b))
            return null;
        if (x.getText().length() == 0)
            return null;
        lastFind = x.getText();
        lastFindCaseSensitive = c.getModel().isSelected();
        lastFindForward = !b.getModel().isSelected();
        doFindNext();
        return null;
    }

    /** This method performs Edit->FindNext. */
    private Runner doFindNext() {
        if (wrap)
            return wrapMe();
        if (lastFind.length() == 0)
            return null;
        OurSyntaxWidget t = text.get();
        String all = t.getText();
        int i = Util.indexOf(all, lastFind, t.getCaret() + (lastFindForward ? 0 : -1), lastFindForward, lastFindCaseSensitive);
        if (i < 0) {
            i = Util.indexOf(all, lastFind, lastFindForward ? 0 : (all.length() - 1), lastFindForward, lastFindCaseSensitive);
            if (i < 0) {
                log.logRed("The specified search string cannot be found.");
                return null;
            }
            log.logRed("Search wrapped.");
        } else {
            log.clearError();
        }
        if (lastFindForward)
            t.moveCaret(i, i + lastFind.length());
        else
            t.moveCaret(i + lastFind.length(), i);
        t.requestFocusInWindow();
        return null;
    }

    /** This method performs Edit->Preferences. */
    public Runner doPreferences() {
        if (wrap)
            return wrapMe();
        prefDialog.setVisible(true);
        return null;
    }

    /**
     * This method applies the look and feel stored in a user preference. Default
     * look and feel for Mac and Windows computers is "Native", and for other is
     * "Cross-platform".
     */
    private Runner doLookAndFeel() {
        if (wrap)
            return wrapMe();
        try {
            if ("Native".equals(LAF.get())) {
                UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
            } else {
                UIManager.setLookAndFeel(UIManager.getCrossPlatformLookAndFeelClassName());
            }
            SwingUtilities.updateComponentTreeUI(frame);
            SwingUtilities.updateComponentTreeUI(prefDialog);
            SwingUtilities.updateComponentTreeUI(viz.getFrame());
        } catch (Throwable e) {}
        return null;
    }

    /** This method performs Edit->Goto. */
    private Runner doGoto() {
        if (wrap)
            return wrapMe();
        JTextField y = OurUtil.textfield("", 10);
        JTextField x = OurUtil.textfield("", 10);
        if (!OurDialog.getInput("Go To", "Line Number:", y, "Column Number (optional):", x))
            return null;
        try {
            OurSyntaxWidget t = text.get();
            int xx = 1, yy = Integer.parseInt(y.getText()), lineCount = t.getLineCount();
            if (yy < 1)
                return null;
            if (yy > lineCount) {
                log.logRed("This file only has " + lineCount + " line(s).");
                return null;
            }
            if (x.getText().length() != 0)
                xx = Integer.parseInt(x.getText());
            if (xx < 1) {
                log.logRed("If the column number is specified, it must be 1 or greater.");
                return null;
            }
            int caret = t.getLineStartOffset(yy - 1);
            int len = (yy == lineCount ? t.getText().length() + 1 : t.getLineStartOffset(yy)) - caret;
            if (xx > len)
                xx = len;
            if (xx < 1)
                xx = 1;
            t.moveCaret(caret + xx - 1, caret + xx - 1);
            t.requestFocusInWindow();
        } catch (NumberFormatException ex) {
            log.logRed("The number must be 1 or greater.");
        } catch (Throwable ex) {
            // This error is not important
        }
        return null;
    }

    /** This method performs Edit->GotoPrevFile. */
    private Runner doGotoPrevFile() {
        if (wrap)
            return wrapMe();
        else {
            text.prev();
            return null;
        }
    }

    /** This method performs Edit->GotoNextFile. */
    private Runner doGotoNextFile() {
        if (wrap)
            return wrapMe();
        else {
            text.next();
            return null;
        }
    }

    // ===============================================================================================================//
    //colorful merge
    /** This method refreshes the "run" menu. */
    private Runner doRefreshmerge() {
        if (wrap)
            return wrapMe();
        Map<String,Map<Map<Integer,Pos>,Sig>> cp = sigs;
        JMenu mergeSigs,mergeField,remMultiplicity,remAbstract;
         mergeSigs=new JMenu("Merge Sigs");
         mergeField=new JMenu("Merge Field");
         remMultiplicity=new JMenu("Remove remMultiplicity");
         remAbstract=new JMenu("Remove Abstract");
        //存储所有的sig
        SafeList<Sig> sigSafeList=new SafeList<>();
        //parser the model to get sigs
        if (cp == null) {
            Module world = null;
            try {
                int resolutionMode = (Version.experimental && ImplicitThis.get()) ? 2 : 1;
                A4Options opt = new A4Options();
                opt.tempDirectory = alloyHome() + fs + "tmp";
                opt.solverDirectory = alloyHome() + fs + "binary";
                opt.originalFilename = Util.canon(text.get().getFilename());
                world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, text.takeSnapshot(), opt.originalFilename, resolutionMode);
            } catch (Err er) {
                text.shade(er.pos);
                log.logRed(er.toString() + "\n\n");
                return null;
            }
            cp=world.getcolorfulSigSet();
            sigs=cp;
        }

        text.clearShade();
        log.clearError(); // To clear any residual error message

        mergemenu.removeAll();
        mergemenu.add(mergeSigs);
        mergemenu.add(mergeField);
        mergemenu.add(remMultiplicity);
        mergemenu.add(remAbstract);

        //1. merge sig 菜单
        // 计算可以进行合并的sig ,Map <sig,Arraylist>
        for(Map m:cp.values()){
            sigSafeList.addAll(m.values());
        }
        Iterator<Map.Entry<String, Map<Map<Integer,Pos>,Sig>>> entries = cp.entrySet().iterator();
        Map<Sig, ArrayList<Sig>> sigList=new HashMap();
        Map<Field, ArrayList<Field>> fieldList=new HashMap();

        while (entries.hasNext()) {
            Map.Entry<String, Map<Map<Integer,Pos>,Sig>> entry = entries.next();

            for(Sig s:sigSafeList){
                ArrayList<Sig> sigArray=new ArrayList<>();
                if(entry.getKey().equals(s.label.substring(5))){
                    for (Map.Entry<Map<Integer,Pos>, Sig> en : entry.getValue().entrySet()){
                        if(!en.getValue().equals(s))
                        if(compare((en.getValue().color.keySet()),s.color.keySet(),new HashSet<>())){
                            sigArray.add(en.getValue());
                        }
                    }
                }
                if(sigArray.size()>0)
                    sigList.put(s,sigArray);
            }
            //计算可以merge的Field
            for (Map.Entry<Map<Integer,Pos>, Sig> en : entry.getValue().entrySet()){
                //计算可以merge的Field
                if(en.getValue().getFields().size()>1){
                    for (Field f: en.getValue().getFields()){
                        ArrayList<Field>  fieldArray=new ArrayList<>();
                        for(Field f2: en.getValue().getFields()){
                            if(!f2.equals(f))
                                if(f.label.equals(f2.label)){
                                    //表达式相同
                                    if(f.decl().expr.isSame(f2.decl().expr)){
                                        if(f.color.keySet().equals(f2.color.keySet())||compare(f.color.keySet(),f2.color.keySet(),new HashSet<>())){
                                            fieldArray.add(f2);
                                        }

                                    }
                                }
                        }
                        if(!fieldArray.isEmpty())
                            fieldList.put(f,fieldArray);

                    }
                }
            }

        }

        //根据sigList生成菜单，
        if(sigList.isEmpty())
            mergemenu.remove(mergeSigs);
        for(Map.Entry<Sig,ArrayList<Sig>> m:sigList.entrySet()){
            JMenu sig=new JMenu(m.getKey().label.substring(5)+" "+getColorString(m.getKey().color.keySet()));
            for(Sig sigSub:m.getValue()){
                JMenuItem y = new JMenuItem(sigSub.label.substring(5) + " " + getColorString(sigSub.color.keySet()), null);
                y.addActionListener(new ActionListener() {
                    @Override
                    public void actionPerformed(ActionEvent e) {
                        //获得父菜单SIG，
                       // Sig parentSig=m.getKey();
                        //获得当前菜单的sig
                       // sigSub;
                        //进行merge
                        domerge(m.getKey(),sigSub);
                    }
                });
                sig.add(y);
            }
            mergeSigs.add(sig);
        }
        //根据fieldList 生成菜单
        if(fieldList.isEmpty())
            mergemenu.remove(mergeField);
        for(Map.Entry<Field,ArrayList<Field>> f:fieldList.entrySet()){
            JMenu field=new JMenu(f.getKey().label+": "+getColorString(f.getKey().color.keySet()));
            for(Field fieSub:f.getValue()){
                JMenuItem y = new JMenuItem(fieSub.label + ": " + getColorString(fieSub.color.keySet()), null);
                y.addActionListener(new ActionListener() {
                    @Override
                    public void actionPerformed(ActionEvent e) {
                        domerge(f.getKey(),fieSub);
                    }
                });
                field.add(y);
            }
            mergeField.add(field);
        }
        
        //生成 remove multiplicity 菜单
        Set <Sig> multSig=new HashSet<>();
        Set <Sig> abstractSig=new HashSet<>();
        Set<Field> multFie=new HashSet<>();
        for(Sig s:sigSafeList){
            if(s.isLone!=null){
                multSig.add(s);
            }
            if(s.isOne!=null){
                multSig.add(s);
            }
            if(s.isSome!=null){
                multSig.add(s);
            }
            if(s.isAbstract!=null){
                abstractSig.add(s);
            }
            for(Field fie:s.getFields()){
                Expr e=fie.decl().expr;
                if(e instanceof ExprUnary &&((ExprUnary) e).op.equals(ExprUnary.Op.NOOP)){
                    Expr exprSub=((ExprUnary) e).sub;
                    if(exprSub instanceof ExprUnary){
                        if(((ExprUnary) exprSub).op.equals(ExprUnary.Op.LONE)||
                                ((ExprUnary) exprSub).op.equals(ExprUnary.Op.ONE)||
                                ((ExprUnary) exprSub).op.equals(ExprUnary.Op.SOME) )
                                    multFie.add(fie);
                    }else if(exprSub instanceof ExprBinary){
                        if(((ExprBinary) exprSub).op.isArrow){
                            if(!((ExprBinary) exprSub).op.equals(ExprBinary.Op.ARROW))
                                multFie.add(fie);
                        }
                    }
                }
            }
        }

        if(multSig.isEmpty()&&multFie.isEmpty())
            mergemenu.remove(remMultiplicity);
        for(Sig sMul:multSig){
            JMenuItem y = new JMenuItem(sMul.label.substring(5) + " " + getColorString(sMul.color.keySet()), null);
            y.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    doRmMultipilicity(sMul);
                }

                private void doRmMultipilicity(Sig sig) {
                    StringBuilder coloF,colorB;
                    coloF=new StringBuilder();
                    colorB=new StringBuilder();
                    if(sig.color!=null)
                        printcolor(coloF,colorB,sig.color.keySet());

                    StringBuilder factString=new StringBuilder();
                    factString.append("fact { ");

                    if (sig.isLone!=null){
                        text.changeText(sig.isLone);
                        factString.append("one "+ sig.label.substring(5)+" ");
                    }
                    if(sig.isOne!=null){
                        text.changeText(sig.isOne);
                        factString.append("one "+ sig.label.substring(5)+" ");
                    }
                    if(sig.isSome!=null){
                        text.changeText(sig.isSome);
                        factString.append("some "+ sig.label.substring(5)+" ");
                    }
                    factString.append("}");
                    text.appendText("\r\n"+coloF+factString+colorB);
                }
            });
            remMultiplicity.add(y);
        }
        for(Field fMul:multFie){
            JMenuItem y = new JMenuItem(fMul.label + ": " + getColorString(fMul.color.keySet()), null);
            y.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    doRmMultipilicity(fMul);
                }

                private void doRmMultipilicity(Field f) {
                    Expr e= null;
                    if(f.decl().expr instanceof ExprUnary ){
                      e=  ((ExprUnary) f.decl().expr).sub;

                        if(e instanceof ExprUnary){
                            if(((ExprUnary) e).op.equals(SOMEOF)){
                                System.out.println("some");
                            }
                        }else if(e instanceof ExprBinary && ((ExprBinary) e).op.isArrow){

                        }
                    }



                }
            });
            remMultiplicity.add(y);
        }

        if(abstractSig.isEmpty())
            mergemenu.remove(remAbstract);
        for(Sig sMul:abstractSig){
            JMenuItem y = new JMenuItem(sMul.label.substring(5) + " " + getColorString(sMul.color.keySet()), null);

            y.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    doRmAbstract(sMul);
                }

                private void doRmAbstract(Sig sig) {
                    if (sig.isAbstract!=null){
                        text.changeText(sig.isAbstract);
                        Set <Sig> children=new HashSet<>();
                        for (Sig s:sigSafeList){
                            if(!sig.equals(s)){
                                if(s instanceof Sig.PrimSig){
                                    if (((Sig.PrimSig) s).parent.equals(sig)){
                                        children.add(s);
                                    }
                                }
                            }
                        }

                        StringBuilder coloF,colorB;
                        coloF=new StringBuilder();
                        colorB=new StringBuilder();
                        if(sig.color!=null)
                            printcolor(coloF,colorB,sig.color.keySet());


                        if(children.isEmpty())
                            text.appendText("\r\n"+coloF+"fact{no "+sig.label.substring(5)+" }"+colorB);
                        else{
                            StringBuilder childString=new StringBuilder();
                            for(Sig child:children){
                                childString.append(child.label.substring(5)+"+");
                            }
                            childString.deleteCharAt(childString.length()-1);




                        text.appendText("\r\n"+coloF+"fact{ "+sig.label.substring(5)+"="+childString+"}"+colorB);
                        }
                    }

                }
            });
            remAbstract.add(y);
//            remAbstract.addMenuListener(new MenuListener() {
//                @Override
//                public void menuSelected(MenuEvent e) {
//                    text.get().shade();
//                }
//
//                @Override
//                public void menuDeselected(MenuEvent e) {
//
//                }
//
//                @Override
//                public void menuCanceled(MenuEvent e) {
//                }
//            });
        }
        return null;
    }
//colorful merge
    private void domerge(Sig key, Sig sigSub) {
        Set<Integer> k=new HashSet<>();
        ArrayList<Sig> tomerge=new ArrayList<>();
        tomerge.add(key);
        tomerge.add(sigSub);

            if(compare(key.color.keySet(),sigSub.color.keySet(),k));
            if(k.size()==1){
                //位置问题
                Sig s=mergelaw(tomerge,k.iterator().next());

                StringBuilder print = new StringBuilder();
                printsigs(new ArrayList<Sig>(){{add(s);}},print);
                for (Map.Entry<Integer,Pos> ent:key.color.entrySet()){
                    key.pos=key.pos.merge(ent.getValue());
                }
                for (Map.Entry<Integer,Pos> ent:sigSub.color.entrySet()){
                    sigSub.pos=sigSub.pos.merge(ent.getValue());
                }

                // sig 位置添加为空白
                text.changeText(key.pos,sigSub.pos);
                text.appendText(print.toString());
                //text.changeText(key.pos,print.toString());
        }

    }
    private void domerge(Field key, Field fieldSub) {
        if(key.color.keySet().equals(fieldSub.color.keySet())){
            if(key.pos.x<fieldSub.pos.x||(key.pos.x==fieldSub.pos.x&& key.pos.y<fieldSub.pos.y)){
                getFieldPos(key);
                text.changeText(key.pos);}
            else {
                getFieldPos(fieldSub);
                text.changeText(fieldSub.pos);
            }
            return;
        }

        Set<Integer> k=new HashSet<>();
        ArrayList<Field> tomerge=new ArrayList<>();
        tomerge.add(key);
        tomerge.add(fieldSub);

        if(compare(key.color.keySet(),fieldSub.color.keySet(),k));
        if(k.size()==1){
            //位置问题
            int colk=key.color.keySet().contains(k.iterator().next())?k.iterator().next():-k.iterator().next();
            Pos p=key.color.get(colk);
            key.color.remove(colk);
            Pos p1=new Pos(p.filename,p.x,p.y,p.x+1,p.y);
            Pos p2=new Pos(p.filename,p.x2,p.y2,p.x2+1,p.y2);
            text.changeText(p1,p2);

            //删除第二个Field
            getFieldPos(fieldSub);
            text.changeText(fieldSub.pos);

        }

    }

    //merge the pos of feature annotations
    private void getFieldPos(Field f) {
        Map<Integer,Pos> sc=new HashMap<>(f.color);
        for(Map.Entry<Integer,Pos> en:f.color.entrySet()){
            if(!f.sig.color.containsValue(en.getValue())){
                f.pos=f.pos.merge(en.getValue());
            }
        }
    }

    private String emptyString(Pos pos) {
        int leng=pos.end()-pos.start();
        StringBuilder blank=new StringBuilder();
        for(int i=0;i<pos.end()-pos.start()+1;i++){
            blank.append(" ");
        }
        return blank.toString();
    }


    /** This method refreshes the "run" menu. */
    private Runner doRefreshRun() {
        if (wrap)
            return wrapMe();
        KeyStroke ac = KeyStroke.getKeyStroke(VK_E, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask());
        try {
            wrap = true;
            runmenu.removeAll();
            menuItem(runmenu, "Execute Latest Command", 'E', 'E', doExecuteLatest());
            runmenu.add(new JSeparator());
            menuItem(runmenu, "Show Latest Instance", 'L', 'L', doShowLatest(), latestInstance.length() > 0);
            menuItem(runmenu, "Show Metamodel", 'M', 'M', doShowMetaModel());
            if (Version.experimental)
                menuItem(runmenu, "Show Parse Tree", 'P', doShowParseTree());
            menuItem(runmenu, "Open Evaluator", 'V', doLoadEvaluator());
        } finally {
            wrap = false;
        }
        List<Command> cp = commands;
        if (cp == null) {
            try {
                String source = text.get().getText();
                cp = CompUtil.parseOneModule_fromString(source);
            } catch (Err e) {
                commands = null;
                runmenu.getItem(0).setEnabled(false);
                runmenu.getItem(3).setEnabled(false);
                text.shade(new Pos(text.get().getFilename(), e.pos.x, e.pos.y, e.pos.x2, e.pos.y2));
                if (AlloyCore.isDebug() && VerbosityPref.get() == Verbosity.FULLDEBUG)
                    log.logRed("Fatal Exception!" + e.dump() + "\n\n");
                else
                    log.logRed(e.toString() + "\n\n");
                return null;
            } catch (Throwable e) {
                commands = null;
                runmenu.getItem(0).setEnabled(false);
                runmenu.getItem(3).setEnabled(false);
                log.logRed("Cannot parse the model.\n" + e.toString() + "\n\n");
                return null;
            }
            commands = cp;
        }
        text.clearShade();
        log.clearError(); // To clear any residual error message
        if (cp == null) {
            runmenu.getItem(0).setEnabled(false);
            runmenu.getItem(3).setEnabled(false);
            return null;
        }
        if (cp.size() == 0) {
            runmenu.getItem(0).setEnabled(false);
            return null;
        }
        if (latestCommand >= cp.size())
            latestCommand = cp.size() - 1;
        runmenu.remove(0);
        try {
            wrap = true;
            for (int i = 0; i < cp.size(); i++) {
                JMenuItem y = new JMenuItem(cp.get(i).toString(), null);
                y.addActionListener(doRun(i));
                if (i == latestCommand) {
                    y.setMnemonic(VK_E);
                    y.setAccelerator(ac);
                }
                runmenu.add(y, i);
            }
            if (cp.size() >= 2) {
                JMenuItem y = new JMenuItem("Execute All", null);
                y.setMnemonic(VK_A);
                y.addActionListener(doRun(-1));
                runmenu.add(y, 0);
                runmenu.add(new JSeparator(), 1);
            }
        } finally {
            wrap = false;
        }
        return null;
    }

    /**
     * This method executes a particular RUN or CHECK command.
     */
    private Runner doRun(Integer commandIndex) {
        if (wrap)
            return wrapMe(commandIndex);
        final int index = commandIndex;
        if (WorkerEngine.isBusy())
            return null;
        if (index == (-2))
            subrunningTask = 1;
        else
            subrunningTask = 0;
        latestAutoInstance = "";
        if (index >= 0)
            latestCommand = index;
        if (index == -1 && commands != null) {
            latestCommand = commands.size() - 1;
            if (latestCommand < 0)
                latestCommand = 0;
        }
        // To update the accelerator to point to the command actually chosen
        doRefreshRun();
        OurUtil.enableAll(runmenu);
        if (commands == null)
            return null;
        if (commands.size() == 0 && index != -2 && index != -3) {
            log.logRed("There are no commands to execute.\n\n");
            return null;
        }
        int i = index;
        if (i >= commands.size())
            i = commands.size() - 1;
        SimpleCallback1 cb = new SimpleCallback1(this, null, log, VerbosityPref.get().ordinal(), latestAlloyVersionName, latestAlloyVersion);
        SimpleTask1 task = new SimpleTask1();
        A4Options opt = new A4Options();
        opt.tempDirectory = alloyHome() + fs + "tmp";
        opt.solverDirectory = alloyHome() + fs + "binary";
        opt.recordKodkod = RecordKodkod.get();
        opt.noOverflow = NoOverflow.get();
        opt.unrolls = Version.experimental ? Unrolls.get() : (-1);
        opt.skolemDepth = SkolemDepth.get();
        opt.coreMinimization = CoreMinimization.get();
        opt.inferPartialInstance = InferPartialInstance.get();
        opt.coreGranularity = CoreGranularity.get();
        opt.originalFilename = Util.canon(text.get().getFilename());
        opt.solver = Solver.get();
        task.bundleIndex = i;
        task.bundleWarningNonFatal = WarningNonfatal.get();
        task.map = text.takeSnapshot();
        task.options = opt.dup();
        task.resolutionMode = (Version.experimental && ImplicitThis.get()) ? 2 : 1;
        task.tempdir = maketemp();
        try {
            runmenu.setEnabled(false);
            runbutton.setVisible(false);
            showbutton.setEnabled(false);
            stopbutton.setVisible(true);
            int newmem = SubMemory.get(), newstack = SubStack.get();
            if (newmem != subMemoryNow || newstack != subStackNow)
                WorkerEngine.stop();
            if (AlloyCore.isDebug() && VerbosityPref.get() == Verbosity.FULLDEBUG)
                WorkerEngine.runLocally(task, cb);
            else
                WorkerEngine.run(task, newmem, newstack, alloyHome() + fs + "binary", "", cb);
            subMemoryNow = newmem;
            subStackNow = newstack;
        } catch (Throwable ex) {
            WorkerEngine.stop();
            log.logBold("Fatal Error: Solver failed due to unknown reason.\n" + "One possible cause is that, in the Options menu, your specified\n" + "memory size is larger than the amount allowed by your OS.\n" + "Also, please make sure \"java\" is in your program path.\n");
            log.logDivider();
            log.flush();
            doStop(2);
        }
        return null;
    }

    /**
     * This method stops the current run or check (how==0 means DONE, how==1 means
     * FAIL, how==2 means STOP).
     */
    Runner doStop(Integer how) {
        if (wrap)
            return wrapMe(how);
        int h = how;
        if (h != 0) {
            if (h == 2 && WorkerEngine.isBusy()) {
                WorkerEngine.stop();
                log.logBold("\nSolving Stopped.\n");
                log.logDivider();
            }
            WorkerEngine.stop();
        }
        runmenu.setEnabled(true);
        runbutton.setVisible(true);
        showbutton.setEnabled(true);
        stopbutton.setVisible(false);
        if (latestAutoInstance.length() > 0) {
            String f = latestAutoInstance;
            latestAutoInstance = "";
            if (subrunningTask == 2)
                viz.loadXML(f, true);
            else if (AutoVisualize.get() || subrunningTask == 1)
                doVisualize("XML: " + f);
        }
        return null;
    }

    /** This method executes the latest command. */
    private Runner doExecuteLatest() {
        if (wrap)
            return wrapMe();
        doRefreshRun();
        OurUtil.enableAll(runmenu);
        if (commands == null)
            return null;
        int n = commands.size();
        if (n <= 0) {
            log.logRed("There are no commands to execute.\n\n");
            return null;
        }
        if (latestCommand >= n)
            latestCommand = n - 1;
        if (latestCommand < 0)
            latestCommand = 0;
        return doRun(latestCommand);
    }

    /** This method displays the parse tree. */
    private Runner doShowParseTree() {
        if (wrap)
            return wrapMe();
        doRefreshRun();
        OurUtil.enableAll(runmenu);
        if (commands != null) {
            Module world = null;
            try {
                int resolutionMode = (Version.experimental && ImplicitThis.get()) ? 2 : 1;
                A4Options opt = new A4Options();
                opt.tempDirectory = alloyHome() + fs + "tmp";
                opt.solverDirectory = alloyHome() + fs + "binary";
                opt.originalFilename = Util.canon(text.get().getFilename());
                world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, text.takeSnapshot(), opt.originalFilename, resolutionMode);
            } catch (Err er) {
                text.shade(er.pos);
                log.logRed(er.toString() + "\n\n");
                return null;
            }
            world.showAsTree(this);
        }
        return null;
    }

    /** This method displays the meta model. */
    private Runner doShowMetaModel() {
        if (wrap)
            return wrapMe();
        doRefreshRun();
        OurUtil.enableAll(runmenu);
        if (commands != null)
            doRun(-2);
        return null;
    }

    /** This method displays the latest instance. */
    private Runner doShowLatest() {
        if (wrap)
            return wrapMe();
        if (latestInstance.length() == 0)
            log.logRed("No previous instances are available for viewing.\n\n");
        else
            doVisualize("XML: " + latestInstance);
        return null;
    }

    /**
     * This method happens when the user tries to load the evaluator from the main
     * GUI.
     */
    private Runner doLoadEvaluator() {
        if (wrap)
            return wrapMe();
        log.logRed("Note: the evaluator is now in the visualizer.\n" + "Just click the \"Evaluator\" toolbar button\n" + "when an instance is shown in the visualizer.\n");
        log.flush();
        return null;
    }

    // ===============================================================================================================//

    /**
     * This method refreshes the "Window" menu for either the SimpleGUI window
     * (isViz==false) or the VizGUI window (isViz==true).
     */
    private Runner doRefreshWindow(Boolean isViz) {
        if (wrap)
            return wrapMe(isViz);
        try {
            wrap = true;
            JMenu w = (isViz ? windowmenu2 : windowmenu);
            w.removeAll();
            if (isViz) {
                viz.addMinMaxActions(w);
            } else {
                menuItem(w, "Minimize", 'M', doMinimize(), iconNo);
                menuItem(w, "Zoom", doZoom(), iconNo);
            }
            w.addSeparator();
            int i = 0;
            for (String f : text.getFilenames()) {
                JMenuItem it = new JMenuItem("Model: " + slightlyShorterFilename(f) + (text.modified(i) ? " *" : ""), null);
                it.setIcon((f.equals(text.get().getFilename()) && !isViz) ? iconYes : iconNo);
                it.addActionListener(f.equals(text.get().getFilename()) ? doShow() : doOpenFile(f));
                w.add(it);
                i++;
            }
            if (viz != null)
                for (String f : viz.getInstances()) {
                    JMenuItem it = new JMenuItem("Instance: " + viz.getInstanceTitle(f), null);
                    it.setIcon((isViz && f.equals(viz.getXMLfilename())) ? iconYes : iconNo);
                    it.addActionListener(doVisualize("XML: " + f));
                    w.add(it);
                }
        } finally {
            wrap = false;
        }
        return null;
    }

    /** This method minimizes the window. */
    private Runner doMinimize() {
        if (wrap)
            return wrapMe();
        else {
            OurUtil.minimize(frame);
            return null;
        }
    }

    /**
     * This method alternatingly maximizes or restores the window.
     */
    private Runner doZoom() {
        if (wrap)
            return wrapMe();
        else {
            OurUtil.zoom(frame);
            return null;
        }
    }

    /** This method bring this window to the foreground. */
    private Runner doShow() {
        if (wrap)
            return wrapMe();
        OurUtil.show(frame);
        text.get().requestFocusInWindow();
        return null;
    }

    // ===============================================================================================================//

    /** This method refreshes the "Option" menu. */
    private Runner doRefreshOption() {
        if (wrap)
            return wrapMe();
        try {
            wrap = true;
            optmenu.removeAll();
            addToMenu(optmenu, Welcome);

            optmenu.addSeparator();

            addToMenu(optmenu, WarningNonfatal);
            addToMenu(optmenu, SubMemory, SubStack, VerbosityPref);

            optmenu.addSeparator();

            addToMenu(optmenu, SyntaxDisabled);
            addToMenu(optmenu, FontSize);
            menuItem(optmenu, "Font: " + FontName.get() + "...", doOptFontname());
            addToMenu(optmenu, TabSize);
            if (Util.onMac() || Util.onWindows())
                menuItem(optmenu, "Use anti-aliasing: Yes", false);
            else
                addToMenu(optmenu, AntiAlias);
            addToMenu(optmenu, A4Preferences.LAF);

            optmenu.addSeparator();

            addToMenu(optmenu, Solver);
            addToMenu(optmenu, SkolemDepth);
            JMenu cmMenu = addToMenu(optmenu, CoreMinimization);
            cmMenu.setEnabled(Solver.get() == SatSolver.MiniSatProverJNI);
            JMenu cgMenu = addToMenu(optmenu, CoreGranularity);
            cgMenu.setEnabled(Solver.get() == SatSolver.MiniSatProverJNI);

            addToMenu(optmenu, AutoVisualize, RecordKodkod);

            if (Version.experimental) {
                addToMenu(optmenu, Unrolls);
                addToMenu(optmenu, ImplicitThis, NoOverflow, InferPartialInstance);
            }

        } finally {
            wrap = false;
        }
        return null;
    }

    private Runner doOptFontname() {
        if (wrap)
            return wrapMe();
        int size = FontSize.get();
        String f = OurDialog.askFont();
        if (f.length() > 0) {
            FontName.set(f);
            text.setFont(f, size, TabSize.get());
            status.setFont(new Font(f, Font.PLAIN, size));
            log.setFontName(f);
        }
        return null;
    }

    /**
     * This method applies the changes to the font-related settings.
     */
    private Runner doOptRefreshFont() {
        if (wrap)
            return wrapMe();
        String f = FontName.get();
        int n = FontSize.get();
        text.setFont(f, n, TabSize.get());
        status.setFont(new Font(f, Font.PLAIN, n));
        log.setFontSize(n);
        viz.doSetFontSize(n);
        return null;
    }

    /** This method toggles the "antialias" checkbox. */
    private Runner doOptAntiAlias() {
        if (!wrap) {
            OurAntiAlias.enableAntiAlias(AntiAlias.get());
        }
        return wrapMe();
    }

    /**
     * This method toggles the "syntax highlighting" checkbox.
     */
    private Runner doOptSyntaxHighlighting() {
        if (!wrap) {
            text.enableSyntax(!SyntaxDisabled.get());
        }
        return wrapMe();
    }

    // ===============================================================================================================//
//    //colorful merge
//    /** This method refreshes the "Refactor" menu. */
//    private Runner doRefreshRefactor() {
//        if (wrap)
//            return wrapMe();
//        try {
//            wrap = true;
//        } finally {
//            wrap = false;
//        }
//
//        Map cp = sigs;
//
//        //parser the model to get sigs
//        if (cp == null) {
//            Module world = null;
//            try {
//                int resolutionMode = (Version.experimental && ImplicitThis.get()) ? 2 : 1;
//                A4Options opt = new A4Options();
//                opt.tempDirectory = alloyHome() + fs + "tmp";
//                opt.solverDirectory = alloyHome() + fs + "binary";
//                opt.originalFilename = Util.canon(text.get().getFilename());
//                world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, text.takeSnapshot(), opt.originalFilename, resolutionMode);
//            } catch (Err er) {
//                text.shade(er.pos);
//                log.logRed(er.toString() + "\n\n");
//                return null;
//            }
//            cp=world.getcolorfulSigSet();
//            sigs=cp;
//        }
//
//        text.clearShade();
//        log.clearError(); // To clear any residual error message
//        if (cp == null) {
//            refactormenu.getItem(0).setEnabled(false);
//            refactormenu.getItem(3).setEnabled(false);
//            return null;
//        }
//        if (cp.size() == 0) {
//            refactormenu.getItem(0).setEnabled(false);
//            return null;
//        }
//
//        refactormenu.removeAll();
//        try {
//            wrap = true;
//
//            //define meanue bar
//            Iterator<Map.Entry<String, Map<Map<Integer,Pos>,Sig>>> entries = cp.entrySet().iterator();
//            while (entries.hasNext()) {
//                Map.Entry<String, Map<Map<Integer,Pos>,Sig>> entry = entries.next();
//
//                String[] color= new String [entry.getValue().size()];
//
//                int j=0;
//                for (Map.Entry<Map<Integer,Pos>, Sig> en : entry.getValue().entrySet()) {
//                    if(en.getKey().size()==0)
//                        color [j]=en.getValue().label.substring(5);
//                    else{
//                        String feaname=getColorString(en.getKey().keySet());
//                        color [j]=en.getValue().label.substring(5) +" "+ feaname;
//                    }
//                    j++;
//                }
//                A4Preferences.StringChoicePref Signame   = new A4Preferences.StringChoicePref("SigName", "Sig "+entry.getKey(), Arrays.asList(color), "");
//
//                //add Listener to Jmenue bar
//                Signame.addChangeListener(new ChangeListener() {
//                    @Override
//                    public void stateChanged(ChangeEvent e) {
//                        Set<Integer> color=new HashSet<>();
//
//                        //get click button's String[sigName color list ]
//                        if(!Signame.get().isEmpty()){
//                            String [] string=Signame.get().split("\\s+");
//
//                            //get click sigs's color
//                            if(sigs!=null){
//                                if(string.length>1)
//                                    for(int k=1;k<string.length;k++)
//                                        color.add(Integer.parseInt(string[k]));
//                            }
//
//                            //get the sig map, <color,sig>
//                            Map<Map<Integer,Pos>,Sig> map=new HashMap<>();
//                            if (string.length>=1)
//                                map= sigs.get(string[0]);
//
//
//                            //remove extra sigs,need to add fields
//                            if(color.size()==0){
//                                Iterator<Map.Entry<Map<Integer,Pos>, Sig>> it = map.entrySet().iterator();
//                                ArrayList<Field> fields=new ArrayList<>();
//                                while(it.hasNext()){
//                                    Map.Entry<Map<Integer,Pos>, Sig> entry = it.next();
//
//                                    if(!entry.getKey().isEmpty()){
//                                        fields.addAll(entry.getValue().getFields().makeCopy()) ;
//                                        it.remove();//使用迭代器的remove()方法删除元素
//                                    }
//
//                                    //deal with fields
//                                }
//                                //不是base sig
//                            }else {
//                                Sig sig=null;
//
//                                //查找点击的Sig
//                                Iterator<Map.Entry<Map<Integer,Pos>, Sig>> it = map.entrySet().iterator();
//                                while(it.hasNext()){
//                                    Map.Entry<Map<Integer,Pos>, Sig> entry = it.next();
//                                    if(entry.getKey().keySet().equals(color)) {
//                                        sig = entry.getValue();
//                                        break;
//                                    }
//                                    else
//                                        continue;
//                                }
//
//                                if(sig!=null){
//                                    JPopupMenu jPopupMenuOne=new JPopupMenu();
//                                    JMenu sigMenu=new JMenu("Sig "+sig.label.substring(5) + " " + getColorString(sig.color.keySet()));
//
//                                    ArrayList<Sig> sigToMerge=new ArrayList();
//                                    sigToMerge.add(sig);
//
//                                    Map mapclone=new HashMap(map);
//                                    Iterator<Map.Entry<Map<Integer,Pos>, Sig>> itmap = mapclone.entrySet().iterator();
//                                    while(itmap.hasNext()){
//                                        Map.Entry<Map<Integer,Pos>, Sig> entry = itmap.next();
//                                        if(!entry.getValue().equals(sig)) {
//                                            HashSet<Integer> k=new HashSet<>();
//                                            if(!sig.equals(entry.getValue()))
//                                            if (compare(sig.color.keySet(), entry.getValue().color.keySet(),k)) {
//                                                JMenuItem y = new JMenuItem("Sig "+entry.getValue().label.substring(5) + " " + getColorString(entry.getKey().keySet()), null);
//
//                                                sigToMerge.add(entry.getValue());
//                                                Map<Map<Integer,Pos>, Sig> finalMap = map;
//                                                Sig finalSig = sig;
////                                                y.addMouseMotionListener(new MouseMotionListener() {
////                                                    @Override
////                                                    public void mouseDragged(MouseEvent e) {
////
////                                                    }
////
////                                                    @Override
////                                                    public void mouseMoved(MouseEvent e) {
////                                                        text.get()
////
////                                                    }
////                                                });
//                                                y.addActionListener(new ActionListener() {
//
//                                                    public void actionPerformed(ActionEvent e) {
//                                                        String [] string=y.getText().split("\\s+");
//                                                        ArrayList<Sig> sigToMergecolon=new ArrayList<>();
//                                                        sigToMergecolon.add(finalSig);
//                                                        if(string.length>2){
//                                                            Set<Integer> co=new HashSet<>();
//                                                            for(int k=2;k<string.length;k++)
//                                                                co.add(Integer.parseInt(string[k]));
//                                                            for(Sig s: sigToMerge){
//                                                                if(co.equals(s.color.keySet()))
//                                                                    sigToMergecolon.add(s);
//                                                            }
//                                                        }
//                                                        doRefactor(finalMap,sigToMergecolon,sigs);
//                                                    }
//                                                });
//
//                                                //y.addActionListener(doRefactor(map,sigToMerge,sigs));
//                                                sigMenu.add(y);
//                                            }
//
//                                        }
//                                    }
//                                    if(sigMenu.getMenuComponentCount()==0)
//                                        sigMenu =new JMenu("Can not apply merge law !");
//
//                                    sigMenu.setComponentOrientation(ComponentOrientation.LEFT_TO_RIGHT);
//                                    sigMenu.setHorizontalAlignment(SwingConstants.LEFT);
//                                    jPopupMenuOne.add(sigMenu);
//                                    jPopupMenuOne.show(text.get().getComponent(),540,10);
//
//
//                                }
//                            }
//
//
//
//
////                        if (string.length>0){
////                            if(sigs.containsKey(string[0])){
////                                for (Map.Entry<Set<Integer>, Sig> entry : map.entrySet()) {
////                                    if(string.length==1)
////                                    System.out.println("Key = " + entry.getKey() + ", Value = " + entry.getValue());
////                                    if(entry.getKey().isEmpty())
////                                        System.out.println("!!!!!!Key =null  " + ", Value = " + entry.getValue());
////                                }
////                            }
////                            System.out.println(string.toString());
////                        }
//                        }
//                    }
//                });
//                addToMenu(refactormenu, Signame);
//
//
//            }
//        } finally {
//            wrap = false;
//        }
//        return null;
//    }

    /**
     * print sigs
     */
    public  void printsigs(ArrayList<Sig> finalsig,StringBuilder print){
        for(Sig s: finalsig){
            StringBuilder coloF,colorB,coloFieldF,colorFieldB;
             coloF=new StringBuilder();
             colorB=new StringBuilder();
            if(s.color!=null)
                printcolor(coloF,colorB,s.color.keySet());

            print.append(coloF);

            if(s.isAbstract!=null)
                print.append("abstract ");
            if(s.isLone !=null)
                print.append("lone ");
            if (s.isOne!=null)
                print.append("one ");
            if(s.isSome != null)
                print.append("some ");

            print.append("sig "+ s.label.substring(5));

            if(s.isSubsig!=null ){
                if(((Sig.PrimSig) s).parent!=UNIV){
                    print.append(" extends ");
                    print.append( ((Sig.PrimSig) s).parent.label.substring(5));
                }
            }

            if(s.isSubset!=null){
                print.append(" in ");
                print.append(((Sig.SubsetSig) s).parents.get(0).label.substring(5));

                if(((Sig.SubsetSig) s).parents.size()>1){
                    for (int j = 1; j< ((Sig.SubsetSig) s).parents.size()-1; j ++){
                        print.append(" + "+((Sig.SubsetSig) s).parents.get(j).label.substring(5));
                    }
                }
            }
            //print fields
            print.append("{ ");

            for (Decl f:s.getFieldDecls()){
                coloFieldF=new StringBuilder();
                colorFieldB =new StringBuilder();
                if(f.color!=null){
                    Map<Integer,Pos> fcol=new HashMap<>(f.color);
                    if(s.color!=null)
                   for (Map.Entry<Integer,Pos> col:s.color.entrySet()){
                           fcol.remove(col.getKey());
                    }

                    printcolor(coloFieldF,colorFieldB,fcol.keySet());
                }
                print.append("\r\n        "+coloFieldF);
                print.append(f.disjoint!=null? "disj ": "");
                if(f.names.size()>=1){
                    for(ExprHasName n:f.names){
                        print.append(n.label+",");
                    }
                    print.deleteCharAt(print.length()-1);
                    print.append(": ");

                    //get the first Field
                    Sig.Field n= (Sig.Field)f.names.get(0);
                    print.append( n.decl().expr.toString().replace("this/",""));
                    print.append(colorFieldB);
                    print.append(",");
                }
            }

            if(!s.getFieldDecls().isEmpty()){
                print.deleteCharAt(print.length()-1);
                //} of Sig
                print.append("\r\n        }");
            }else
                //} of Sig
                print.append("}");

            //fact for sig
            if(!s.getFacts().isEmpty()){
                print.append("{");
                for(Expr fact:s.getFacts()){
                    String temp=fact.toString();
                    //replace "s.fileld" to field
                    temp=temp.replace(s.label.substring(5)+" .","");
                    print.append("\r\n        "+temp);
                }
                print.append("\r\n        }\r\n");
            }

            print.append(colorB);
            //print.append("\r\n");
        }
    }

    //colorful merge
    /**
     * print color annotation, for example clor: -1,2,3, colfront :➊➁➂
     * @param colfront record the front color annotation:➂➁➊
     * @param colback record the back color annotation
     * @param color  colors in the expression
     */
    private void printcolor(StringBuilder colfront, StringBuilder colback, Set<Integer> color) {
        final String PFEAT1="\u2780";
        final String PFEAT2="\u2781";
        final String PFEAT3="\u2782" ;
        final String PFEAT4="\u2783" ;
        final String PFEAT5="\u2784" ;
        final String PFEAT6="\u2785" ;
        final String PFEAT7="\u2786" ;
        final String PFEAT8="\u2787" ;
        final String PFEAT9="\u2788" ;
        final String NFEAT1="\u278A" ;
        final String NFEAT2="\u278B" ;
        final String NFEAT3="\u278C" ;
        final String NFEAT4="\u278D" ;
        final String NFEAT5="\u278E" ;
        final String NFEAT6="\u278F" ;
        final String NFEAT7="\u2790" ;
        final String NFEAT8="\u2791" ;
        final String NFEAT9="\u2792" ;
        for(Integer i: color){
            if(i==1) {
                colfront.append(PFEAT1+" ");
                colback.insert(0,PFEAT1);
            }else if(i==2) {
                colfront.append(PFEAT2+" ");
                colback.insert(0,PFEAT2);
            }else if(i==3) {
                colfront.append(PFEAT3+" ");
                colback.insert(0,PFEAT3);
            }else if(i==4) {
                colfront.append(PFEAT4+" ");
                colback.insert(0,PFEAT4);
            }else if(i==5) {
                colfront.append(PFEAT5+" ");
                colback.insert(0,PFEAT5);
            }else if(i==6) {
                colfront.append(PFEAT6+" ");
                colback.insert(0,PFEAT6);
            }else if(i==7) {
                colfront.append(PFEAT7+" ");
                colback.insert(0,PFEAT7);
            }else if(i==8) {
                colfront.append(PFEAT8+" ");
                colback.insert(0,PFEAT8);
            }else if(i==9) {
                colfront.append(PFEAT9+" ");
                colback.insert(0,PFEAT9);
            }else if(i==-1) {
                colfront.append(NFEAT1+" ");
                colback.insert(0,NFEAT1);
            }else if(i==-2) {
                colfront.append(NFEAT2+" ");
                colback.insert(0,NFEAT2);
            }else if(i==-3) {
                colfront.append(NFEAT3+" ");
                colback.insert(0,NFEAT3);
            }else if(i==-4) {
                colfront.append(NFEAT4+" ");
                colback.insert(0,NFEAT4);
            }else if(i==-5) {
                colfront.append(NFEAT5+" ");
                colback.insert(0,NFEAT5);
            }else if(i==-6) {
                colfront.append(NFEAT6+" ");
                colback.insert(0,NFEAT6);
            }else if(i==-7) {
                colfront.append(NFEAT7+" ");
                colback.insert(0,NFEAT7);
            }else if(i==-8) {
                colfront.append(NFEAT8+" ");
                colback.insert(0,NFEAT8);
            }else if(i==-9) {
                colfront.append(NFEAT9+" ");
                colback.insert(0,NFEAT9);
            }

            if(colfront!=null)
                colfront.deleteCharAt(colfront.length()-1);
        }
        return;
    }

    private ActionListener doRefactor(Map map,ArrayList<Sig> toMerge,Map <String,Map<Map<Integer,Pos>,Sig> >sigs) {
        if (wrap)
            return wrapMe();
        Set<Integer> k=new HashSet<>();
        if(toMerge.size()>=2){
            Sig sig1=toMerge.get(0);
            Sig sig2=toMerge.get(1);
            if(compare(toMerge.get(0).color.keySet(),toMerge.get(1).color.keySet(),k));
            if(k.size()==1){
                Sig s=mergelaw(toMerge,k.iterator().next());
                if(s!=null)
                    map.put(s.color,s);

                //delete  mereged sigs
                Iterator<Map.Entry<Map<Integer,Pos>, Sig>> it = map.entrySet().iterator();
                while(it.hasNext()){
                    Map.Entry<Map<Integer,Pos>, Sig> entry = it.next();
                    if(entry.getValue().equals(sig1)|| entry.getValue().equals(sig2))
                        it.remove();//使用迭代器的remove()方法删除元素
                }
            }

            //Repaint
            ArrayList<Sig> finalsig=new ArrayList<>();
            Iterator<Map.Entry<String, Map<Map<Integer,Pos>,Sig>>> entries = sigs.entrySet().iterator();
            while (entries.hasNext()) {
                Map.Entry<String, Map<Map<Integer,Pos>,Sig>> entry = entries.next();

                finalsig.addAll(entry.getValue().values());
                StringBuilder print = new StringBuilder();
                if(finalsig.size()>0)
                    printsigs(finalsig,print);
                text.get().setText(print.toString());

            }
        }
        return null;
    }

    /**
     * merge law,to merge sigs
     * @param tomerge two sigs need to be merge
     * @param k  feature to be remove
     */
    private static Sig mergelaw( ArrayList<Sig> tomerge,Integer k){
        if(tomerge.size()==2) {
            Sig sig1 = tomerge.get(0);
            Sig sig2 = tomerge.get(1);
            //used to generate new Sig
            Attr[] attributes = new Attr[sig1.attributes.size()];
            for (int i = 0; i < sig1.attributes.size(); i++) {
                attributes[i] = sig1.attributes.get(i);
            }
            Sig signew = new Sig.PrimSig(sig1.label, ((Sig.PrimSig) sig1).parent, attributes);

            Map<Integer,Pos> feats=new HashMap<>(sig1.color);
            feats.remove(k);
            feats.remove(-k);
            signew.color.putAll(feats);
            //合并Fields
            VisitQuery<Expr> sigold2newVisitor = new VisitQuery<Expr>() {

                @Override
                public  Expr visit(ExprCall x) {
                    return x;
                }

                @Override
                public Expr visit(ExprBinary x) throws Err {
                    visitThis(x.left);
                    visitThis(x.right);
                    return x;
                }

                @Override
                public Expr visit(ExprList x) throws Err {
                    for(Expr e: x.args)
                        visitThis(e);
                    return x;
                }

                @Override
                public Expr visit(ExprConstant x) throws Err {
                    return x;
                }

                @Override
                public Expr visit(ExprITE x) throws Err {
                    visitThis(x.cond);
                    visitThis(x.left);
                    visitThis(x.right);
                    return x;
                }

                @Override
                public Expr visit(ExprLet x) throws Err {
                    visitThis(x.expr);
                    visitThis(x.sub);
                    return x;
                }

                @Override
                public Expr visit(ExprQt x) throws Err {
                    return x;
                }

                @Override
                public Expr visit(ExprUnary x) throws Err {
                    visitThis(x.sub);
                    return x;
                }

                @Override
                public Expr visit(ExprVar x) throws Err {
                    return x;
                }

                @Override
                public Expr visit(Sig x) throws Err {
                    if (x.equals(sig1)||x.equals(sig2))
                        return signew;
                    return x;
                }

                @Override
                public Expr visit(Field x) throws Err {
                    return x;
                }
            };


            for (Decl d: sig1.getFieldDecls()){
                Expr exprNew=d.expr.accept(sigold2newVisitor);
                String[]labels = new String[d.names.size()];
                for(int i=0; i< d.names.size();i++){
                    labels[i]=d.names.get(i).label;
                }
                signew.addTrickyField(d.span(),d.isPrivate,d.disjoint,d.disjoint2,null,labels,exprNew,d.color);
            }
            for (Decl d: sig2.getFieldDecls()){
                Expr exprNew=d.expr.accept(sigold2newVisitor);
                String[]labels = new String[d.names.size()];
                for(int i=0; i< d.names.size();i++){
                    labels[i]=d.names.get(i).label;
                }
                signew.addTrickyField(d.span(),d.isPrivate,d.disjoint,d.disjoint2,null,labels,exprNew,d.color);
            }

            return signew;
        }
        return null;
    }
//colorful merge
    /**
     * find two sigs can apply law.
     * return true if find match
     */
    private static boolean compare( Set<Integer> feats1,  Set<Integer> feats2,Set<Integer> k){
        boolean match=false;
        //if(sig1.equals(sig2))
         //   return match;
        //Set<Integer> feats1=sig1.color.keySet();
       // Set<Integer> feats2=sig2.color.keySet();
        if(feats1.size()!=feats2.size())
            return match;

        for(int i: feats1){
            if(feats2.contains(i) || feats2.contains(-i)){
                for(int j:feats2){
                    if(i==-j){
                        if(k.size()<1){
                            k.add(j>0?j:-j);
                            break;
                        } else{
                            k.clear();
                            return match;}
                    }else if(i==j){
                        break;
                    }
                }
            }
        }
        match=true;
        return match;
    }



    private String getColorString(Set<Integer> key) {
        String name=null;
        for (Integer i:key){
            String color=null;
            if(i==1) color ="\u2780";
            else if(i==2) color ="\u2781";
            else if(i==3) color ="\u2782" ;
            else if(i==4) color ="\u2783" ;
            else if(i==5) color ="\u2784" ;
            else if(i==6) color ="\u2785" ;
            else if(i==7) color ="\u2786" ;
            else if(i==8) color ="\u2787" ;
            else if(i==9) color ="\u2788" ;
            else if(i==-1) color ="\u278A" ;
            else if(i==-2) color ="\u278B" ;
            else if(i==-3) color ="\u278C" ;
            else if(i==-4) color ="\u278D" ;
            else if(i==-5) color ="\u278E" ;
            else if(i==-6) color ="\u278F" ;
            else if(i==-7) color ="\u2790" ;
            else if(i==-8) color ="\u2791" ;
            else if(i==-9) color ="\u2792" ;

            name=name==null? color : name+" "+color;
        }
        return name;
    }

    // ===============================================================================================================//

    /** This method displays the about box. */
    public Runner doAbout() {
        if (wrap)
            return wrapMe();
        OurDialog.showmsg("About Alloy Analyzer " + Version.version(), OurUtil.loadIcon("images/logo.gif"), "Alloy Analyzer " + Version.version(), "Build date: " + " git: " + Version.commit, " ", "Lead developer: Felix Chang", "Engine developer: Emina Torlak", "Graphic design: Julie Pelaez", "Project lead: Daniel Jackson", " ", "Please post comments and questions to the Alloy Community Forum at http://alloy.mit.edu/", " ", "Thanks to: Ilya Shlyakhter, Manu Sridharan, Derek Rayside, Jonathan Edwards, Gregory Dennis,", "Robert Seater, Edmond Lau, Vincent Yeung, Sam Daitch, Andrew Yip, Jongmin Baek, Ning Song,", "Arturo Arizpe, Li-kuo (Brian) Lin, Joseph Cohen, Jesse Pavel, Ian Schechter, and Uriel Schafer.");
        return null;
    }

    /** This method displays the help html. */
    private Runner doHelp() {
        if (wrap)
            return wrapMe();
        try {
            int w = OurUtil.getScreenWidth(), h = OurUtil.getScreenHeight();
            final JFrame frame = new JFrame();
            final JEditorPane html1 = new JEditorPane("text/html", "");
            final JEditorPane html2 = new JEditorPane("text/html", "");
            final HTMLDocument doc1 = (HTMLDocument) (html1.getDocument());
            doc1.setAsynchronousLoadPriority(-1);
            final HTMLDocument doc2 = (HTMLDocument) (html2.getDocument());
            doc2.setAsynchronousLoadPriority(-1);
            html1.setPage(this.getClass().getResource("/help/Nav.html"));
            html2.setPage(this.getClass().getResource("/help/index.html"));
            HyperlinkListener hl = new HyperlinkListener() {

                @Override
                public final void hyperlinkUpdate(HyperlinkEvent e) {
                    try {
                        if (e.getEventType() != HyperlinkEvent.EventType.ACTIVATED)
                            return;
                        if (e.getURL().getPath().endsWith("quit.htm")) {
                            frame.dispose();
                            return;
                        }
                        HTMLDocument doc = (HTMLDocument) (html2.getDocument());
                        doc.setAsynchronousLoadPriority(-1); // So that we can
                                                            // catch any
                                                            // exception
                                                            // that may
                                                            // occur
                        html2.setPage(e.getURL());
                        html2.requestFocusInWindow();
                    } catch (Throwable ex) {}
                }
            };
            html1.setEditable(false);
            html1.setBorder(new EmptyBorder(3, 3, 3, 3));
            html1.addHyperlinkListener(hl);
            html2.setEditable(false);
            html2.setBorder(new EmptyBorder(3, 3, 3, 3));
            html2.addHyperlinkListener(hl);
            JScrollPane scroll1 = OurUtil.scrollpane(html1);
            JScrollPane scroll2 = OurUtil.scrollpane(html2);
            JSplitPane split = OurUtil.splitpane(JSplitPane.HORIZONTAL_SPLIT, scroll1, scroll2, 150);
            split.setResizeWeight(0d);
            frame.setTitle("Alloy Analyzer Online Guide");
            frame.getContentPane().setLayout(new BorderLayout());
            frame.getContentPane().add(split, BorderLayout.CENTER);
            frame.pack();
            frame.setSize(w - w / 10, h - h / 10);
            frame.setLocation(w / 20, h / 20);
            frame.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            frame.setVisible(true);
            html2.requestFocusInWindow();
        } catch (Throwable ex) {
            return null;
        }
        return null;
    }

    /** This method displays the license box. */
    private Runner doLicense() {
        if (wrap)
            return wrapMe();
        final String JAR = Util.jarPrefix();
        String alloytxt;
        try {
            alloytxt = Util.readAll(JAR + "LICENSES" + File.separator + "Alloy.txt");
        } catch (IOException ex) {
            return null;
        }
        final JTextArea text = OurUtil.textarea(alloytxt, 15, 85, false, false, new EmptyBorder(2, 2, 2, 2), new Font("Monospaced", Font.PLAIN, 12));
        final JScrollPane scroll = OurUtil.scrollpane(text, new LineBorder(Color.DARK_GRAY, 1));
        final JComboBox combo = new OurCombobox(new String[] {
                                                              "Alloy", "Kodkod", "JavaCup", "SAT4J", "ZChaff", "MiniSat"
        }) {

            private static final long serialVersionUID = 0;

            @Override
            public void do_changed(Object value) {
                if (value instanceof String) {
                    try {
                        String content = Util.readAll(JAR + "LICENSES" + File.separator + value + ".txt");
                        text.setText(content);
                    } catch (IOException ex) {
                        text.setText("Sorry: an error has occurred in displaying the license file.");
                    }
                }
                text.setCaretPosition(0);
            }
        };
        OurDialog.showmsg("Copyright Notices", "The source code for the Alloy Analyzer is available under the MIT license.", " ", "The Alloy Analyzer utilizes several third-party packages whose code may", "be distributed under a different license. We are extremely grateful to", "the authors of these packages for making their source code freely available.", " ", OurUtil.makeH(null, "See the copyright notice for: ", combo, null), " ", scroll);
        return null;
    }

    /** This method changes the latest instance. */
    void doSetLatest(String arg) {
        latestInstance = arg;
        latestAutoInstance = arg;
    }

    /**
     * The color to use for functions/predicate/paragraphs that contains part of the
     * unsat core.
     */
    final Color supCoreColor = new Color(0.95f, 0.1f, 0.1f);

    /** The color to use for the unsat core. */
    final Color coreColor    = new Color(0.9f, 0.4f, 0.4f);

    /**
     * The color to use for functions/predicate used by the Unsat core.
     */
    final Color subCoreColor = new Color(0.9f, 0.7f, 0.7f);

    /**
     * This method displays a particular instance or message.
     */
    @SuppressWarnings("unchecked" )
    Runner doVisualize(String arg) {
        if (wrap)
            return wrapMe(arg);
        text.clearShade();
        if (arg.startsWith("MSG: ")) { // MSG: message
            OurDialog.showtext("Detailed Message", arg.substring(5));
        }
        if (arg.startsWith("CORE: ")) { // CORE: filename
            String filename = Util.canon(arg.substring(6));
            Pair<Set<Pos>,Set<Pos>> hCore;
            // Set<Pos> lCore;
            InputStream is = null;
            ObjectInputStream ois = null;
            try {
                is = new FileInputStream(filename);
                ois = new ObjectInputStream(is);
                hCore = (Pair<Set<Pos>,Set<Pos>>) ois.readObject();
                // lCore = (Set<Pos>) ois.readObject();
            } catch (Throwable ex) {
                log.logRed("Error reading or parsing the core \"" + filename + "\"\n");
                return null;
            } finally {
                Util.close(ois);
                Util.close(is);
            }
            text.clearShade();
            text.shade(hCore.b, subCoreColor, false);
            text.shade(hCore.a, coreColor, false);
            // shade again, because if not all files were open, some shadings
            // will have no effect
            text.shade(hCore.b, subCoreColor, false);
            text.shade(hCore.a, coreColor, false);
        }
        if (arg.startsWith("POS: ")) { // POS: x1 y1 x2 y2 filename
            Scanner s = new Scanner(arg.substring(5));
            int x1 = s.nextInt(), y1 = s.nextInt(), x2 = s.nextInt(), y2 = s.nextInt();
            String f = s.nextLine();
            if (f.length() > 0 && f.charAt(0) == ' ')
                f = f.substring(1); // Get rid of the space after Y2
            Pos p = new Pos(Util.canon(f), x1, y1, x2, y2);
            text.shade(p);
        }
        if (arg.startsWith("CNF: ")) { // CNF: filename
            String filename = Util.canon(arg.substring(5));
            try {
                String text = Util.readAll(filename);
                OurDialog.showtext("Text Viewer", text);
            } catch (IOException ex) {
                log.logRed("Error reading the file \"" + filename + "\"\n");
            }
        }
        if (arg.startsWith("XML: ")) { // XML: filename
            viz.loadXML(Util.canon(arg.substring(5)), false);
        }

        if(arg.startsWith("als: ")){//colorful Alloy
            doOpenFile(arg.substring(5)); //colorful Alloy
        }
        return null;
    }

    /** This method opens a particular file. */
    private Runner doOpenFile(String arg) {
        if (wrap)
            return wrapMe(arg);
        String f = Util.canon(arg);
        if (!text.newtab(f))
            return null;
        if (text.get().isFile())
            addHistory(f);
        doShow();
        text.get().requestFocusInWindow();
        log.clearError();
        return null;
    }

    /** This object performs solution enumeration. */
    private final Computer enumerator = new Computer() {

        @Override
        public String compute(Object input) {
            final String arg = (String) input;
            OurUtil.show(frame);
            if (WorkerEngine.isBusy())
                throw new RuntimeException("Alloy4 is currently executing a SAT solver command. Please wait until that command has finished.");
            SimpleCallback1 cb = new SimpleCallback1(SimpleGUI.this, viz, log, VerbosityPref.get().ordinal(), latestAlloyVersionName, latestAlloyVersion);
            SimpleTask2 task = new SimpleTask2();
            task.filename = arg;
            try {
                if (AlloyCore.isDebug())
                    WorkerEngine.runLocally(task, cb);
                else
                    WorkerEngine.run(task, SubMemory.get(), SubStack.get(), alloyHome() + fs + "binary", "", cb);
                // task.run(cb);
            } catch (Throwable ex) {
                WorkerEngine.stop();
                log.logBold("Fatal Error: Solver failed due to unknown reason.\n" + "One possible cause is that, in the Options menu, your specified\n" + "memory size is larger than the amount allowed by your OS.\n" + "Also, please make sure \"java\" is in your program path.\n");
                log.logDivider();
                log.flush();
                doStop(2);
                return arg;
            }
            subrunningTask = 2;
            runmenu.setEnabled(false);
            runbutton.setVisible(false);
            showbutton.setEnabled(false);
            stopbutton.setVisible(true);
            return arg;
        }
    };

    /** Converts an A4TupleSet into a SimTupleset object. */
    private static SimTupleset convert(Object object) throws Err {
        if (!(object instanceof A4TupleSet))
            throw new ErrorFatal("Unexpected type error: expecting an A4TupleSet.");
        A4TupleSet s = (A4TupleSet) object;
        if (s.size() == 0)
            return SimTupleset.EMPTY;
        List<SimTuple> list = new ArrayList<SimTuple>(s.size());
        int arity = s.arity();
        for (A4Tuple t : s) {
            String[] array = new String[arity];
            for (int i = 0; i < t.arity(); i++)
                array[i] = t.atom(i);
            list.add(SimTuple.make(array));
        }
        return SimTupleset.make(list);
    }

    /** Converts an A4Solution into a SimInstance object. */
    private static SimInstance convert(Module root, A4Solution ans) throws Err {
        SimInstance ct = new SimInstance(root, ans.getBitwidth(), ans.getMaxSeq());
        for (Sig s : ans.getAllReachableSigs()) {
            if (!s.builtin)
                ct.init(s, convert(ans.eval(s)));
            for (Field f : s.getFields())
                if (!f.defined)
                    ct.init(f, convert(ans.eval(f)));
        }
        for (ExprVar a : ans.getAllAtoms())
            ct.init(a, convert(ans.eval(a)));
        for (ExprVar a : ans.getAllSkolems())
            ct.init(a, convert(ans.eval(a)));
        return ct;
    }

    /** This object performs expression evaluation. */
    private static Computer evaluator = new Computer() {

        private String filename = null;

        @Override
        public final Object compute(final Object input) throws Exception {
            if (input instanceof File) {
                filename = ((File) input).getAbsolutePath();
                return "";
            }
            if (!(input instanceof String))
                return "";
            final String str = (String) input;
            if (str.trim().length() == 0)
                return ""; // Empty line
            Module root = null;
            A4Solution ans = null;
            try {
                Map<String,String> fc = new LinkedHashMap<String,String>();
                XMLNode x = new XMLNode(new File(filename));
                if (!x.is("alloy"))
                    throw new Exception();
                String mainname = null;
                for (XMLNode sub : x)
                    if (sub.is("instance")) {
                        mainname = sub.getAttribute("filename");
                        break;
                    }
                if (mainname == null)
                    throw new Exception();
                for (XMLNode sub : x)
                    if (sub.is("source")) {
                        String name = sub.getAttribute("filename");
                        String content = sub.getAttribute("content");
                        fc.put(name, content);
                    }
                root = CompUtil.parseEverything_fromFile(A4Reporter.NOP, fc, mainname, (Version.experimental && ImplicitThis.get()) ? 2 : 1);
                ans = A4SolutionReader.read(root.getAllReachableSigs(), x);
                for (ExprVar a : ans.getAllAtoms()) {
                    root.addGlobal(a.label, a);
                }
                for (ExprVar a : ans.getAllSkolems()) {
                    root.addGlobal(a.label, a);
                }
            } catch (Throwable ex) {
                throw new ErrorFatal("Failed to read or parse the XML file.");
            }
            try {
                Expr e = CompUtil.parseOneExpression_fromString(root, str);
                if (AlloyCore.isDebug() && VerbosityPref.get() == Verbosity.FULLDEBUG) {
                    SimInstance simInst = convert(root, ans);
                    if (simInst.wasOverflow())
                        return simInst.visitThis(e).toString() + " (OF)";
                }
                return ans.eval(e);
            } catch (HigherOrderDeclException ex) {
                throw new ErrorType("Higher-order quantification is not allowed in the evaluator.");
            }
        }
    };

    // ====== Main Method ====================================================//

    /**
     * Main method that launches the program; this method might be called by an
     * arbitrary thread.
     */
    public static void main(final String[] args) throws Exception {

        List<String> remainingArgs = new ArrayList<>();

        if (args.length > 0) {
            boolean help = false;
            boolean quit = false;

            for (String cmd : args) {
                switch (cmd) {

                    case "--worker" :
                    case "-w" :
                        WorkerEngine.main(args);
                        break;

                    case "--version" :
                    case "-v" :
                        System.out.println(Version.version());
                        break;

                    case "--help" :
                    case "-h" :
                    case "-?" :
                        help = true;
                        break;

                    case "--debug" :
                    case "-d" :
                        System.setProperty("debug", "yes");
                        break;

                    case "--quit" :
                    case "-q" :
                        quit = true;
                        break;

                    default :
                        if (cmd.endsWith(".als"))
                            remainingArgs.add(cmd);
                        else {
                            System.out.println("Unknown cmd " + cmd);
                            help = true;
                        }
                        break;
                }
            }

            if (help)
                System.out.println("Usage: alloy [options] file ...\n" + "  //" + "  -d/--debug                  set debug mode\n" + "  -h/--help                   show this help\n" + "  -q/--quit                   do not continue with GUI\n" + "  -v/--version                show version\n");

            if (quit)
                return;
        }

        SwingUtilities.invokeLater(new Runnable() {

            @Override
            public void run() {
                new SimpleGUI(args);
            }
        });
    }

    // ====== Constructor ====================================================//

    // /** Create a dummy task object for testing purpose. */
    // private static final WorkerEngine.WorkerTask dummyTask = new
    // WorkerEngine.WorkerTask() {
    // private static final long serialVersionUID = 0;
    // public void run(WorkerCallback out) { }
    // };

    /**
     * The constructor; this method will be called by the AWT event thread, using
     * the "invokeLater" method.
     */
    private SimpleGUI(final String[] args) {

        UIManager.put("ToolTip.font", new FontUIResource("Courier New", Font.PLAIN, 14));

        // Register an exception handler for uncaught exceptions
        MailBug.setup();

        // Enable better look-and-feel
        if (Util.onMac() || Util.onWindows()) {
            System.setProperty("com.apple.mrj.application.apple.menu.about.name", "Alloy");
            System.setProperty("com.apple.mrj.application.growbox.intrudes", "true");
            System.setProperty("com.apple.mrj.application.live-resize", "true");
            System.setProperty("com.apple.macos.useScreenMenuBar", "true");
            System.setProperty("apple.laf.useScreenMenuBar", "true");
        }
        if (Util.onMac()) {
            macUtil = new MacUtil();
            macUtil.tryAddMenus(this);
        }

        doLookAndFeel();

        // Figure out the desired x, y, width, and height
        int screenWidth = OurUtil.getScreenWidth(), screenHeight = OurUtil.getScreenHeight();
        int width = AnalyzerWidth.get();
        if (width <= 0)
            width = screenWidth / 10 * 8;
        else if (width < 100)
            width = 100;
        if (width > screenWidth)
            width = screenWidth;
        int height = AnalyzerHeight.get();
        if (height <= 0)
            height = screenHeight / 10 * 8;
        else if (height < 100)
            height = 100;
        if (height > screenHeight)
            height = screenHeight;
        int x = AnalyzerX.get();
        if (x < 0)
            x = screenWidth / 10;
        if (x > screenWidth - 100)
            x = screenWidth - 100;
        int y = AnalyzerY.get();
        if (y < 0)
            y = screenHeight / 10;
        if (y > screenHeight - 100)
            y = screenHeight - 100;

        // Put up a slash screen
        final JFrame frame = new JFrame("Alloy Analyzer");
        frame.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        frame.pack();
        if (!Util.onMac() && !Util.onWindows()) {
            String gravity = System.getenv("_JAVA_AWT_WM_STATIC_GRAVITY");
            if (gravity == null || gravity.length() == 0) {
                // many Window managers do not respect ICCCM2; this should help
                // avoid the Title Bar being shifted "off screen"
                if (x < 30) {
                    if (x < 0)
                        x = 0;
                    width = width - (30 - x);
                    x = 30;
                }
                if (y < 30) {
                    if (y < 0)
                        y = 0;
                    height = height - (30 - y);
                    y = 30;
                }
            }
            if (width < 100)
                width = 100;
            if (height < 100)
                height = 100;
        }
        frame.setSize(width, height);
        frame.setLocation(x, y);
        frame.setVisible(true);
        frame.setTitle("Alloy Analyzer " + Version.version() + " loading... please wait...");
        final int windowWidth = width;
        // We intentionally call setVisible(true) first before settings the
        // "please wait" title,
        // since we want the minimized window title on Linux/FreeBSD to just say
        // Alloy Analyzer

        // Test the allowed memory sizes
        // final WorkerEngine.WorkerCallback c = new
        // WorkerEngine.WorkerCallback() {
        // private final List<Integer> allowed = new ArrayList<Integer>();
        // private final List<Integer> toTry = new
        // ArrayList<Integer>(Arrays.asList(256,512,768,1024,1536,2048,2560,3072,3584,4096));
        // private int mem;
        // public synchronized void callback(Object msg) {
        // if (toTry.size()==0) {
        // SwingUtilities.invokeLater(new Runnable() {
        // public void run() { SimpleGUI.this.frame=frame;
        // SimpleGUI.this.finishInit(args, windowWidth); }
        // });
        // return;
        // }
        // try { mem=toTry.remove(0); WorkerEngine.stop();
        // WorkerEngine.run(dummyTask, mem, 128, "", "", this); return; }
        // catch(IOException ex) { fail(); }
        // }
        // public synchronized void done() {
        // //System.out.println("Alloy4 can use "+mem+"M"); System.out.flush();
        // allowed.add(mem);
        // callback(null);
        // }
        // public synchronized void fail() {
        // //System.out.println("Alloy4 cannot use "+mem+"M");
        // System.out.flush();
        // callback(null);
        // }
        // };
        // c.callback(null);

        SimpleGUI.this.frame = frame;
        finishInit(args, windowWidth);
    }

    private void finishInit(String[] args, int width) {

        // Add the listeners
        try {
            wrap = true;
            frame.addWindowListener(doQuit());
        } finally {
            wrap = false;
        }
        frame.addComponentListener(this);

        // initialize the "allowed memory sizes" array
        // allowedMemorySizes = new
        // ArrayList<Integer>(initialAllowedMemorySizes);
        // int newmem = SubMemory.get();
        // if (!allowedMemorySizes.contains(newmem)) {
        // int newmemlen = allowedMemorySizes.size();
        // if (allowedMemorySizes.contains(768) || newmemlen==0)
        // SubMemory.set(768); // a nice default value
        // else
        // SubMemory.set(allowedMemorySizes.get(newmemlen-1));
        // }

        // Choose the appropriate font
        int fontSize = FontSize.get();
        String fontName = OurDialog.getProperFontName(FontName.get(), "Courier New", "Lucidia", "Courier", "Monospaced");
        FontName.set(fontName);

        // Copy required files from the JAR
        copyFromJAR();
        final String binary = alloyHome() + fs + "binary";

        // Create the menu bar
        JMenuBar bar = new JMenuBar();
        try {
            wrap = true;
            filemenu = menu(bar, "&File", doRefreshFile());
            editmenu = menu(bar, "&Edit", doRefreshEdit());
            runmenu = menu(bar, "E&xecute", doRefreshRun());
            optmenu = menu(bar, "&Options", doRefreshOption());
            windowmenu = menu(bar, "&Window", doRefreshWindow(false));
            windowmenu2 = menu(null, "&Window", doRefreshWindow(true));
            helpmenu = menu(bar, "&Help", null);
            if (!Util.onMac())
                menuItem(helpmenu, "About Alloy...", 'A', doAbout());
            menuItem(helpmenu, "Quick Guide", 'Q', doHelp());
            menuItem(helpmenu, "See the Copyright Notices...", 'L', doLicense());
            //colorful merge
          // refactormenu= menu(bar, "R&efactor", doRefreshRefactor());
            mergemenu= menu(bar, "M&erge", doRefreshmerge());
        } finally {
            wrap = false;
        }

        // Pre-load the visualizer
        viz = new VizGUI(false, "", windowmenu2, enumerator, evaluator);
        viz.doSetFontSize(FontSize.get());

        // Create the toolbar
        try {
            wrap = true;
            toolbar = new JToolBar();
            toolbar.setFloatable(false);
            if (!Util.onMac())
                toolbar.setBackground(background);
            toolbar.add(OurUtil.button("New", "Starts a new blank model", "images/24_new.gif", doNew()));
            toolbar.add(OurUtil.button("Open", "Opens an existing model", "images/24_open.gif", doOpen()));
            toolbar.add(OurUtil.button("Reload", "Reload all the models from disk", "images/24_reload.gif", doReloadAll()));
            toolbar.add(OurUtil.button("Save", "Saves the current model", "images/24_save.gif", doSave()));
            toolbar.add(runbutton = OurUtil.button("Execute", "Executes the latest command", "images/24_execute.gif", doExecuteLatest()));
            toolbar.add(stopbutton = OurUtil.button("Stop", "Stops the current analysis", "images/24_execute_abort2.gif", doStop(2)));
            stopbutton.setVisible(false);
            toolbar.add(showbutton = OurUtil.button("Show", "Shows the latest instance", "images/24_graph.gif", doShowLatest()));

            toolbar.add(Box.createHorizontalGlue());
            toolbar.setBorder(new OurBorder(false, false, false, false));
        } finally {
            wrap = false;
        }

        // Choose the antiAlias setting
        OurAntiAlias.enableAntiAlias(AntiAlias.get());

        // Create the message area
        logpane = OurUtil.scrollpane(null);
        log = new SwingLogPanel(logpane, fontName, fontSize, background, Color.BLACK, new Color(.7f, .2f, .2f), this);

        // Create loggers for preference changes
        PreferencesDialog.logOnChange(log, A4Preferences.allUserPrefs().toArray(new Pref< ? >[0]));

        // Create the text area
        text = new OurTabbedSyntaxWidget(fontName, fontSize, TabSize.get());
        text.listeners.add(this);
        text.enableSyntax(!SyntaxDisabled.get());

        // Add everything to the frame, then display the frame
        Container all = frame.getContentPane();
        all.setLayout(new BorderLayout());
        all.removeAll();
        JPanel lefthalf = new JPanel();
        lefthalf.setLayout(new BorderLayout());
        lefthalf.add(toolbar, BorderLayout.NORTH);
        text.addTo(lefthalf, BorderLayout.CENTER);
        splitpane = OurUtil.splitpane(JSplitPane.HORIZONTAL_SPLIT, lefthalf, logpane, width / 2);
        splitpane.setResizeWeight(0.5D);
        status = OurUtil.make(OurAntiAlias.label(" "), new Font(fontName, Font.PLAIN, fontSize), Color.BLACK, background);
        status.setBorder(new OurBorder(true, false, false, false));
        all.add(splitpane, BorderLayout.CENTER);
        all.add(status, BorderLayout.SOUTH);

        // Generate some informative log messages
        log.logBold("Alloy Analyzer " + Version.version() + " (build date: " + Version.buildDate() + " git " + Version.commit + ")\n\n");

        // If on Mac, then register an application listener
        try {
            wrap = true;
            if (Util.onMac()) {
                macUtil.registerApplicationListener(doShow(), doAbout(), doOpenFile(""), doQuit());
            }
        } catch (Throwable t) {
            System.out.println("Mac classes not there");
        } finally {
            wrap = false;
        }

        // Add the new JNI location to the java.library.path
        try {
            System.setProperty("java.library.path", binary);
            // The above line is actually useless on Sun JDK/JRE (see Sun's bug ID 4280189)
            // The following 4 lines should work for Sun's JDK/JRE (though they probably won't work for others)
            String[] newarray = new String[] {
                                              binary
            };
            java.lang.reflect.Field old = ClassLoader.class.getDeclaredField("usr_paths");
            old.setAccessible(true);
            old.set(null, newarray);
        } catch (Throwable ex) {}
        // Pre-load the preferences dialog
        prefDialog = new PreferencesDialog(log, binary);
        prefDialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        try {
            wrap = true;
            prefDialog.addChangeListener(wrapToChangeListener(doOptRefreshFont()), FontName, FontSize, TabSize);
            prefDialog.addChangeListener(wrapToChangeListener(doOptAntiAlias()), AntiAlias);
            prefDialog.addChangeListener(wrapToChangeListener(doOptSyntaxHighlighting()), SyntaxDisabled);
            prefDialog.addChangeListener(wrapToChangeListener(doLookAndFeel()), LAF);
        } finally {
            wrap = false;
        }

        // If the temporary directory has become too big, then tell the user
        // they can "clear temporary directory".
        long space = computeTemporarySpaceUsed();
        if (space < 0 || space >= 20 * 1024768) {
            if (space < 0)
                log.logBold("Warning: Alloy4's temporary directory has exceeded 1024M.\n");
            else
                log.logBold("Warning: Alloy4's temporary directory now uses " + (space / 1024768) + "M.\n");
            log.log("To clear the temporary directory,\n" + "go to the File menu and click \"Clear Temporary Directory\"\n");
            log.logDivider();
            log.flush();
        }

        // Refreshes all the menu items
        doRefreshFile();
        OurUtil.enableAll(filemenu);
        doRefreshEdit();
        OurUtil.enableAll(editmenu);
        doRefreshRun();
        OurUtil.enableAll(runmenu);
        doRefreshOption();
        doRefreshWindow(false);
        OurUtil.enableAll(windowmenu);

        //doRefreshRefactor();//colorful merge
        doRefreshmerge();//colorful merge
        OurUtil.enableAll(mergemenu);

        frame.setJMenuBar(bar);

        // Open the given file, if a filename is given in the command line
        for (String f : args)
            if (f.toLowerCase(Locale.US).endsWith(".als")) {
                File file = new File(f);
                if (file.exists() && file.isFile())
                    doOpenFile(file.getPath());
            }

        // Update the title and status bar
        notifyChange();
        text.get().requestFocusInWindow();

        // Launch the welcome screen if needed
        if (!AlloyCore.isDebug() && Welcome.get()) {
            JCheckBox again = new JCheckBox("Show this message every time you start the Alloy Analyzer");
            again.setSelected(true);
            OurDialog.showmsg("Welcome", "Thank you for using the Alloy Analyzer " + Version.version(), " ", "Version 4 of the Alloy Analyzer is a complete rewrite,", "offering improvements in robustness, performance and usability.", "Models written in Alloy 3 will require some small alterations to run in Alloy 4.", " ", "Here are some quick tips:", " ", "* Function calls now use [ ] instead of ( )", "  For more details, please see http://alloy.mit.edu/alloy4/quickguide/", " ", "* The Execute button always executes the latest command.", "  To choose which command to execute, go to the Execute menu.", " ", "* The Alloy Analyzer comes with a variety of sample models.", "  To see them, go to the File menu and click Open Sample Models.", " ", again);
            doShow();
            Welcome.set(again.isSelected());
        }

        // Periodically ask the MailBug thread to see if there is a newer
        // version or not
        final long now = System.currentTimeMillis();
        final Timer t = new Timer(800, null);
        t.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                int n = MailBug.latestBuildNumber();
                // If beyond 3 seconds, then we should stop because the log
                // message may run into other user messages
                if (System.currentTimeMillis() - now >= 3000 || n <= Version.buildNumber()) {
                    t.stop();
                    return;
                }
                latestAlloyVersion = n;
                latestAlloyVersionName = MailBug.latestBuildName();
                log.logBold("An updated version of the Alloy Analyzer has been released.\n");
                log.log("Please visit alloy.mit.edu to download the latest version:\nVersion " + latestAlloyVersionName + "\n");
                log.logDivider();
                log.flush();
                t.stop();
            }
        });
        t.start();
    }

    /** {@inheritDoc} */
    @Override
    public Object do_action(Object sender, Event e) {
        if (sender instanceof OurTabbedSyntaxWidget)
            switch (e) {
                case FOCUSED :
                    notifyFocusGained();
                    break;
                case STATUS_CHANGE :
                    notifyChange();
                    break;
                default :
                    break;
            }
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public Object do_action(Object sender, Event e, Object arg) {
        if (sender instanceof OurTree && e == Event.CLICK && arg instanceof Browsable) {
            Pos p = ((Browsable) arg).pos();
            if (p == Pos.UNKNOWN)
                p = ((Browsable) arg).span();
            text.shade(p);
        }
        return true;
    }

    /**
     * Creates menu items from boolean preferences (<code>prefs</code>) and adds
     * them to a given parent menu (<code>parent</code>).
     */
    private void addToMenu(JMenu parent, BooleanPref... prefs) {
        for (BooleanPref pref : prefs) {
            Action action = pref.getTitleAction();
            Object name = action.getValue(Action.NAME);
            menuItem(parent, name + ": " + (pref.get() ? "Yes" : "No"), action);
        }
    }

    /**
     * Creates a menu item for each choice preference (from <code>prefs</code>) and
     * adds it to a given parent menu (<code>parent</code>).
     */
    @SuppressWarnings({
                       "rawtypes", "unchecked"
    } )
    private JMenu addToMenu(JMenu parent, ChoicePref... prefs) {
        JMenu last = null;
        for (ChoicePref pref : prefs) {
            last = new JMenu(pref.title + ": " + pref.renderValueShort(pref.get()));
            addSubmenuItems(last, pref);
            parent.add(last);
        }
        return last;
    }

    /**
     * Creates a sub-menu item for each choice of a given preference
     * (<code>pref</code>) and adds it to a given parent menu (<code>parent</code>).
     */
    @SuppressWarnings({
                       "rawtypes", "unchecked"
    } )
    private void addSubmenuItems(JMenu parent, ChoicePref pref) {
        Object selected = pref.get();
        for (Object item : pref.validChoices()) {
            Action action = pref.getAction(item);
            menuItem(parent, pref.renderValueLong(item).toString(), action, item == selected ? iconYes : iconNo);
        }
    }

    /**
     * Takes a <code>Runner</code> and wraps it into a <code>ChangeListener</code>
     */
    private static ChangeListener wrapToChangeListener(final Runner r) {
        assert r != null;
        return new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                r.run();
            }
        };
    }


}
