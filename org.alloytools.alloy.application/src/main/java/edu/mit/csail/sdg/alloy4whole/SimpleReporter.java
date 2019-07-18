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

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.printExpr.*;
import org.alloytools.alloy.core.AlloyCore;

import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerCallback;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerTask;
import edu.mit.csail.sdg.alloy4viz.StaticInstanceReader;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import static edu.mit.csail.sdg.ast.Sig.UNIV;

/** This helper method is used by SimpleGUI. */

final class SimpleReporter extends A4Reporter {
    public static final class SimpleCallback1 implements WorkerCallback {

        private final SimpleGUI         gui;
        private final VizGUI            viz;
        private final SwingLogPanel     span;
        private final Set<ErrorWarning> warnings = new HashSet<ErrorWarning>();
        private final List<String>      results  = new ArrayList<String>();
        private int                     len2     = 0, len3 = 0, verbosity = 0;
        private final String            latestName;
        private final int               latestVersion;

        public SimpleCallback1(SimpleGUI gui, VizGUI viz, SwingLogPanel span, int verbosity, String latestName, int latestVersion) {
            this.gui = gui;
            this.viz = viz;
            this.span = span;
            this.verbosity = verbosity;
            this.latestName = latestName;
            this.latestVersion = latestVersion;
            len2 = len3 = span.getLength();
        }

        @Override
        public void done() {
            if (viz != null)
                span.setLength(len2);
            else
                span.logDivider();
            span.flush();
            gui.doStop(0);
        }

        @Override
        public void fail() {
            span.logBold("\nAn error has occurred!\n");
            span.logDivider();
            span.flush();
            gui.doStop(1);
        }

        @Override
        public void callback(Object msg) {
            if (msg == null) {
                span.logBold("Done\n");
                span.flush();
                return;
            }
            if (msg instanceof String) {
                span.logBold(((String) msg).trim() + "\n");
                span.flush();
                return;
            }
            if (msg instanceof Throwable) {
                for (Throwable ex = (Throwable) msg; ex != null; ex = ex.getCause()) {
                    if (ex instanceof OutOfMemoryError) {
                        span.logBold("\nFatal Error: the solver ran out of memory!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase memory under the Options menu.\n");
                        return;
                    }
                    if (ex instanceof StackOverflowError) {
                        span.logBold("\nFatal Error: the solver ran out of stack space!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase stack under the Options menu.\n");
                        return;
                    }
                }
            }
            if (msg instanceof Err) {
                Err ex = (Err) msg;
                String text = "fatal";
                boolean fatal = false;
                if (ex instanceof ErrorSyntax)
                    text = "syntax";
                else if (ex instanceof ErrorType)
                    text = "type";
                else if(ex instanceof ErrorColor) //colorful Alloy
                    text="feature painted";      //colorful Alloy
                else
                    fatal = true;
                if (ex.pos == Pos.UNKNOWN)
                    span.logBold("A " + text + " error has occurred:  ");
                else
                    span.logLink("A " + text + " error has occurred:  ", "POS: " + ex.pos.x + " " + ex.pos.y + " " + ex.pos.x2 + " " + ex.pos.y2 + " " + ex.pos.filename);
                if (verbosity > 2) {
                    span.log("(see the ");
                    span.logLink("stacktrace", "MSG: " + ex.dump());
                    span.log(")\n");
                } else {
                    span.log("\n");
                }
                span.logIndented(ex.msg.trim());
                span.log("\n");
                if (fatal && latestVersion > Version.buildNumber())
                    span.logBold("\nNote: You are running Alloy build#" + Version.buildNumber() + ",\nbut the most recent is Alloy build#" + latestVersion + ":\n( version " + latestName + " )\nPlease try to upgrade to the newest version," + "\nas the problem may have been fixed already.\n");
                span.flush();
                if (!fatal)
                    gui.doVisualize("POS: " + ex.pos.x + " " + ex.pos.y + " " + ex.pos.x2 + " " + ex.pos.y2 + " " + ex.pos.filename);
                return;
            }
            if (msg instanceof Throwable) {
                Throwable ex = (Throwable) msg;
                span.logBold(ex.toString().trim() + "\n");
                span.flush();
                return;
            }
            if (!(msg instanceof Object[]))
                return;
            Object[] array = (Object[]) msg;
            if (array[0].equals("pop")) {
                span.setLength(len2);
                String x = (String) (array[1]);
                if (viz != null && x.length() > 0)
                    OurDialog.alert(x);
            }
            if (array[0].equals("declare")) {
                gui.doSetLatest((String) (array[1]));
            }
            if (array[0].equals("S2")) {
                len3 = len2 = span.getLength();
                span.logBold("" + array[1]);
            }
            if (array[0].equals("R3")) {
                span.setLength(len3);
                span.log("" + array[1]);
            }
            if (array[0].equals("link")) {
                span.logLink((String) (array[1]), (String) (array[2]));
            }
            if (array[0].equals("bold")) {
                span.logBold("" + array[1]);
            }
            if (array[0].equals("")) {
                span.log("" + array[1]);
            }
            if (array[0].equals("scope") && verbosity > 0) {
                span.log("   " + array[1]);
            }
            if (array[0].equals("bound") && verbosity > 1) {
                span.log("   " + array[1]);
            }
            if (array[0].equals("resultCNF")) {
                results.add(null);
                span.setLength(len3);
                span.log("   File written to " + array[1] + "\n\n");
            }
            if (array[0].equals("debug") && verbosity > 2) {
                span.log("   " + array[1] + "\n");
                len2 = len3 = span.getLength();
            }
            if (array[0].equals("translate")) {
                span.log("   " + array[1]);
                len3 = span.getLength();
                span.logBold("   Generating CNF...\n");
            }
            if (array[0].equals("solve")) {
                span.setLength(len3);
                span.log("   " + array[1]);
                len3 = span.getLength();
                span.logBold("   Solving...\n");
            }
            if (array[0].equals("warnings")) {
                if (warnings.size() == 0)
                    span.setLength(len2);
                else if (warnings.size() > 1)
                    span.logBold("Note: There were " + warnings.size() + " compilation warnings. Please scroll up to see them.\n\n");
                else
                    span.logBold("Note: There was 1 compilation warning. Please scroll up to see them.\n\n");
                if (warnings.size() > 0 && Boolean.FALSE.equals(array[1])) {
                    Pos e = warnings.iterator().next().pos;
                    gui.doVisualize("POS: " + e.x + " " + e.y + " " + e.x2 + " " + e.y2 + " " + e.filename);
                    span.logBold("Warnings often indicate errors in the model.\n" + "Some warnings can affect the soundness of the analysis.\n" + "To proceed despite the warnings, go to the Options menu.\n");
                }
            }
            if (array[0].equals("warning")) {
                ErrorWarning e = (ErrorWarning) (array[1]);
                if (!warnings.add(e))
                    return;
                Pos p = e.pos;
                span.logLink("Warning #" + warnings.size(), "POS: " + p.x + " " + p.y + " " + p.x2 + " " + p.y2 + " " + p.filename);
                span.log("\n");
                span.logIndented(e.msg.trim());
                span.log("\n\n");
            }
            if (array[0].equals("sat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String filename = (String) (array[3]), formula = (String) (array[4]);

                String codefilename= array[6]+".als"; //colorful Alloy
                results.add(filename);
                (new File(filename)).deleteOnExit();
                gui.doSetLatest(filename);
                span.setLength(len3);
                span.log("   ");
                span.logLink(chk ? "Counterexample" : "Instance", "XML: " + filename);
                span.log(" found. ");
                span.logLink(chk ? "Assertion" : "Predicate", formula);
                span.log(chk ? " is invalid" : " is consistent");
                if (expects == 0)
                    span.log(", contrary to expectation");
                else if (expects == 1)
                    span.log(", as expected");
                span.log(". " + array[5] + "ms.\n");
                span.logLink("  Please check the executed code here. ","als: "+codefilename);//colorfull Alloy
                span.log("\r\n\r\n"); //colorful Alloy
            }
            if (array[0].equals("metamodel")) {
                String outf = (String) (array[1]);
                span.setLength(len2);
                (new File(outf)).deleteOnExit();
                gui.doSetLatest(outf);
                span.logLink("Metamodel", "XML: " + outf);
                span.log(" successfully generated.\n\n");
            }
            if (array[0].equals("minimizing")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                span.setLength(len3);
                span.log(chk ? "   No counterexample found." : "   No instance found.");


                if (chk)
                    span.log(" Assertion may be valid");
                else
                    span.log(" Predicate may be inconsistent");
                if (expects == 1)
                    span.log(", contrary to expectation");
                else if (expects == 0)
                    span.log(", as expected");
                span.log(". " + array[4] + "ms.\n");
                span.logBold("   Minimizing the unsat core of " + array[3] + " entries...\n");

                String codefilename = (String) (array[5]); //colorfull Alloy
                span.logLink("  Please check the executed code here. \n","als: "+codefilename);//colorfull Alloy
                span.log("\r\n\r\n"); //colorful Alloy
            }
            if (array[0].equals("unsat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String formula = (String) (array[4]);
                span.setLength(len3);
                span.log(chk ? "   No counterexample found. " : "   No instance found. ");
                span.logLink(chk ? "Assertion" : "Predicate", formula);
                span.log(chk ? " may be valid" : " may be inconsistent");
                if (expects == 1)
                    span.log(", contrary to expectation");
                else if (expects == 0)
                    span.log(", as expected");
                //if (array.length == 5) {
                if (array.length == 6) {  //colorfull Alloy
                    span.log(". " + array[3] + "ms.\n");
                    String codefilename = (String) (array[5]); //colorfull Alloy
                    span.logLink("  Please check the executed code here. \n\n","als: "+codefilename);//colorfull Alloy
                    span.log("\r\n\r\n"); //colorful Alloy
                    span.flush();
                    return;
                }
                String core = (String) (array[5]);
                int mbefore = (Integer) (array[6]), mafter = (Integer) (array[7]);
                span.log(". " + array[3] + "ms.\n");
                if (core.length() == 0) {
                    results.add("");
                    span.log("   No unsat core is available in this case. " + array[8] + "ms.\n\n");
                    String codefilename=(String)(array[9]);//colorfull Alloy
                    span.logLink(" Please check the executed code here. ","als: "+codefilename);//colorfull Alloy
                    span.flush();
                    return;
                }
                results.add(core);
                (new File(core)).deleteOnExit();
                span.log("   ");
                span.logLink("Core", core);
                if (mbefore <= mafter)
                    span.log(" contains " + mafter + " top-level formulas. " + array[8] + "ms.\n\n");
                else
                    span.log(" reduced from " + mbefore + " to " + mafter + " top-level formulas. " + array[8] + "ms.\n\n");
            }
            span.flush();
        }
    }

    private void cb(Serializable... objs) {
        cb.callback(objs);
    }

    /** {@inheritDoc} */
    @Override
    public void resultCNF(final String filename) {
        cb("resultCNF", filename);
    }

    /** {@inheritDoc} */
    @Override
    public void warning(final ErrorWarning ex) {
        warn++;
        cb("warning", ex);
    }

    /** {@inheritDoc} */
    @Override
    public void scope(final String msg) {
        cb("scope", msg);
    }

    /** {@inheritDoc} */
    @Override
    public void bound(final String msg) {
        cb("bound", msg);
    }

    /** {@inheritDoc} */
    @Override
    public void debug(final String msg) {
        cb("debug", msg.trim());
    }

    /** {@inheritDoc} */
    @Override
    public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
        lastTime = System.currentTimeMillis();
        cb("translate", "Solver=" + solver + " Bitwidth=" + bitwidth + " MaxSeq=" + maxseq + (skolemDepth == 0 ? "" : " SkolemDepth=" + skolemDepth) + " Symmetry=" + (symmetry > 0 ? ("" + symmetry) : "OFF") + '\n');
    }

    /** {@inheritDoc} */
    @Override
    public void solve(final int primaryVars, final int totalVars, final int clauses) {
        minimized = 0;
        cb("solve", "" + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses. " + (System.currentTimeMillis() - lastTime +getexecutecodeTime+parserTime) + "ms.\n");
       // cb("solve", "" + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses. " + (System.currentTimeMillis() - lastTime) + "ms.\n");
        lastTime = System.currentTimeMillis();
    }

    /** {@inheritDoc} */
    @Override
    public void resultSAT(Object command, long solvingTime, Object solution) {
        if (!(solution instanceof A4Solution) || !(command instanceof Command))
            return;
        A4Solution sol = (A4Solution) solution;
        Command cmd = (Command) command;
        String formula = recordKodkod ? sol.debugExtractKInput() : "";
        String filename = tempfile + ".xml";
        String codefilename=tempfile.substring(0,tempfile.length()-4); //colorful Alloy
        synchronized (SimpleReporter.class) {
            try {
                cb("R3", "   Writing the XML file...");
                if (latestModule != null)
                    writeXML(this, latestModule, filename, sol, latestKodkodSRC);
            } catch (Throwable ex) {
                cb("bold", "\n" + (ex.toString().trim()) + "\nStackTrace:\n" + (MailBug.dump(ex).trim()) + "\n");
                return;
            }
            latestKodkods.clear();
            latestKodkods.add(sol.toString());
            latestKodkod = sol;
            latestKodkodXML = filename;
        }
        String formulafilename = "";
        if (formula.length() > 0 && tempfile != null) {
            formulafilename = tempfile + ".java";
            try {
                Util.writeAll(formulafilename, formula);
                formulafilename = "CNF: " + formulafilename;
            } catch (Throwable ex) {
                formulafilename = "";
            }
        }
        //cb("sat", cmd.check, cmd.expects, filename, formulafilename, System.currentTimeMillis() - lastTime);
        cb("sat", cmd.check, cmd.expects, filename, formulafilename, System.currentTimeMillis() - lastTime,codefilename); //colorful Alloy
    }

    /** {@inheritDoc} */
    @Override
    public void minimizing(Object command, int before) {
        if (!(command instanceof Command))
            return;
        Command cmd = (Command) command;
        minimized = System.currentTimeMillis();

        String filename = tempfile + ".als"; //colorful Alloy
      //  cb("minimizing", cmd.check, cmd.expects, before, minimized - lastTime);
        cb("minimizing", cmd.check, cmd.expects, before,minimized -lastTime,filename ); //colorful Alloy
    }

    /** {@inheritDoc} */
    @Override
    public void minimized(Object command, int before, int after) {
        minimizedBefore = before;
        minimizedAfter = after;
    }

    /** {@inheritDoc} */
    @Override
    public void resultUNSAT(Object command, long solvingTime, Object solution) {
        if (!(solution instanceof A4Solution) || !(command instanceof Command))
            return;
        A4Solution sol = (A4Solution) solution;
        Command cmd = (Command) command;
        String originalFormula = recordKodkod ? sol.debugExtractKInput() : "";
        String corefilename = "", formulafilename = "";
        if (originalFormula.length() > 0 && tempfile != null) {
            formulafilename = tempfile + ".java";
            try {
                Util.writeAll(formulafilename, originalFormula);
                formulafilename = "CNF: " + formulafilename;
            } catch (Throwable ex) {
                formulafilename = "";
            }
        }
        Pair<Set<Pos>,Set<Pos>> core = sol.highLevelCore();
        if ((core.a.size() > 0 || core.b.size() > 0) && tempfile != null) {
            corefilename = tempfile + ".core";
            OutputStream fs = null;
            ObjectOutputStream os = null;
            try {
                fs = new FileOutputStream(corefilename);
                os = new ObjectOutputStream(fs);
                os.writeObject(core);
                os.writeObject(sol.lowLevelCore());
                corefilename = "CORE: " + corefilename;
            } catch (Throwable ex) {
                corefilename = "";
            } finally {
                Util.close(os);
                Util.close(fs);
            }
        }

        String codefilename = tempfile.substring(0,tempfile.length()-4) + ".als"; //colorful Alloy
        if (minimized == 0)
            cb("unsat", cmd.check, cmd.expects, (System.currentTimeMillis() - lastTime), formulafilename,codefilename);//colorful Alloy
           // cb("unsat", cmd.check, cmd.expects, (System.currentTimeMillis() - lastTime), formulafilename);
        else
            cb("unsat", cmd.check, cmd.expects, minimized - lastTime, formulafilename, corefilename, minimizedBefore, minimizedAfter, (System.currentTimeMillis() - minimized),codefilename);//colorful Alloy
        //cb("unsat", cmd.check, cmd.expects, minimized - lastTime, formulafilename, corefilename, minimizedBefore, minimizedAfter, (System.currentTimeMillis() - minimized));
    }

    private final WorkerCallback cb;

    // ========== These fields should be set each time we execute a set of
    // commands

    /** Whether we should record Kodkod input/output. */
    private final boolean recordKodkod;

    /**
     * The time that the last action began; we subtract it from
     * System.currentTimeMillis() to determine the elapsed time.
     */
    private long          lastTime  = 0;
    // used to compute the time to generate new execute code
    static private  long         getexecutecodeTime=0; //colorful Alloy
    //used to compute code parser time.
    static private  long         parserTime=0; //colorful Alloy

    /**
     * If we performed unsat core minimization, then this is the start of the
     * minimization, else this is 0.
     */
    private long          minimized = 0;

    /** The unsat core size before minimization. */
    private int           minimizedBefore;

    /** The unsat core size after minimization. */
    private int           minimizedAfter;

    /**
     * The filename where we can write a temporary Java file or Core file.
     */
    private String        tempfile  = null;

    // ========== These fields may be altered as each successful command
    // generates a Kodkod or Metamodel instance

    /**
     * The set of Strings already enumerated for this current solution.
     */
    private static final Set<String>       latestKodkods      = new LinkedHashSet<String>();

    /**
     * The A4Solution corresponding to the latest solution generated by Kodkod; this
     * field must be synchronized.
     */
    private static A4Solution              latestKodkod       = null;

    /**
     * The root Module corresponding to this.latestKodkod; this field must be
     * synchronized.
     */
    private static Module                  latestModule       = null;

    /**
     * The source code corresponding to the latest solution generated by Kodkod;
     * this field must be synchronized.
     */
    private static ConstMap<String,String> latestKodkodSRC    = null;

    /**
     * The XML filename corresponding to the latest solution generated by Kodkod;
     * this field must be synchronized.
     */
    private static String                  latestKodkodXML    = null;

    /**
     * The XML filename corresponding to the latest metamodel generated by
     * TranslateAlloyToMetamodel; this field must be synchronized.
     */
    private static String                  latestMetamodelXML = null;

    /** Constructor is private. */
    private SimpleReporter(WorkerCallback cb, boolean recordKodkod) {
        this.cb = cb;
        this.recordKodkod = recordKodkod;
    }

    /** Helper method to write out a full XML file. */
    private static void writeXML(A4Reporter rep, Module mod, String filename, A4Solution sol, Map<String,String> sources) throws Exception {
        sol.writeXML(rep, filename, mod.getAllFunc(), sources);
        if (AlloyCore.isDebug())
            validate(filename);
    }

    private int warn = 0;

    /** Task that performs solution enumeration. */
    static final class SimpleTask2 implements WorkerTask {

        private static final long       serialVersionUID = 0;
        public String                   filename         = "";
        public transient WorkerCallback out              = null;

        private void cb(Object... objs) throws Exception {
            out.callback(objs);
        }

        @Override
        public void run(WorkerCallback out) throws Exception {
            this.out = out;
            cb("S2", "Enumerating...\n");
            A4Solution sol;
            Module mod;
            synchronized (SimpleReporter.class) {
                if (latestMetamodelXML != null && latestMetamodelXML.equals(filename)) {
                    cb("pop", "You cannot enumerate a metamodel.\n");
                    return;
                }
                if (latestKodkodXML == null || !latestKodkodXML.equals(filename)) {
                    cb("pop", "You can only enumerate the solutions of the most-recently-solved command.");
                    return;
                }
                if (latestKodkod == null || latestModule == null || latestKodkodSRC == null) {
                    cb("pop", "Error: the SAT solver that generated the instance has exited,\nso we cannot enumerate unless you re-solve that command.\n");
                    return;
                }
                sol = latestKodkod;
                mod = latestModule;
            }
            if (!sol.satisfiable()) {
                cb("pop", "Error: This command is unsatisfiable,\nso there are no solutions to enumerate.");
                return;
            }
            if (!sol.isIncremental()) {
                cb("pop", "Error: This solution was not generated by an incremental SAT solver.\n" + "Currently only MiniSat and SAT4J are supported.");
                return;
            }
            int tries = 0;
            while (true) {
                sol = sol.next();
                if (!sol.satisfiable()) {
                    cb("pop", "There are no more satisfying instances.\n\n" + "Note: due to symmetry breaking and other optimizations,\n" + "some equivalent solutions may have been omitted.");
                    return;
                }
                String toString = sol.toString();
                synchronized (SimpleReporter.class) {
                    if (!latestKodkods.add(toString))
                        if (tries < 100) {
                            tries++;
                            continue;
                        }
                    // The counter is needed to avoid a Kodkod bug where
                    // sometimes we might repeat the same solution infinitely
                    // number of times; this at least allows the user to keep
                    // going
                    writeXML(null, mod, filename, sol, latestKodkodSRC);

                    latestKodkod = sol;
                }
                cb("declare", filename);
                return;
            }
        }
    }

    /**
     * Validate the given filename to see if it is a valid Alloy XML instance file.
     */
    private static void validate(String filename) throws Exception {
        A4SolutionReader.read(new ArrayList<Sig>(), new XMLNode(new File(filename))).toString();
        StaticInstanceReader.parseInstance(new File(filename));
    }

    /** Task that perform one command. */
    static final class SimpleTask1 implements WorkerTask {

        private static final long serialVersionUID = 0;
        public A4Options          options;
        public String             tempdir;
        public boolean            bundleWarningNonFatal;
        public int                bundleIndex;
        public int                resolutionMode;
        public Map<String,String> map;

        public SimpleTask1() {}

        public void cb(WorkerCallback out, Object... objs) throws IOException {
            out.callback(objs);
        }

        @Override
        public void run(WorkerCallback out) throws Exception {
            cb(out, "S2", "Starting the solver...\n\n");
            final SimpleReporter rep = new SimpleReporter(out, options.recordKodkod);
            final Module world = CompUtil.parseEverything_fromFile(rep, map, options.originalFilename, resolutionMode);
            final List<Sig> sigs = world.getAllReachableSigs();
            final ConstList<Command> cmds = world.getAllCommands();

            //uesed to record features appears in the original module
            Set<Integer> allFeats = new HashSet<>();      //colorful Alloy
            allFeats.addAll(CompModule.feats);           //colorful Alloy(e.g. ➊,➁,allFeats={-1,2})

            cb(out, "warnings", bundleWarningNonFatal);
            if (rep.warn > 0 && !bundleWarningNonFatal)
                return;
            List<String> result = new ArrayList<String>(cmds.size());
            if (bundleIndex == -2) {
                final String outf = tempdir + File.separatorChar + "m.xml";
                cb(out, "S2", "Generating the metamodel...\n");
                PrintWriter of = new PrintWriter(outf, "UTF-8");
                Util.encodeXMLs(of, "\n<alloy builddate=\"", Version.buildDate(), "\">\n\n");
                A4SolutionWriter.writeMetamodel(ConstList.make(sigs), options.originalFilename, of);
                Util.encodeXMLs(of, "\n</alloy>");
                Util.close(of);
                if (AlloyCore.isDebug())
                    validate(outf);
                cb(out, "metamodel", outf);
                synchronized (SimpleReporter.class) {
                    latestMetamodelXML = outf;
                }
            } else
                for (int i = 0; i < cmds.size(); i++)
                    if (bundleIndex < 0 || i == bundleIndex) {
                        synchronized (SimpleReporter.class) {
                            latestModule = world;
                            latestKodkodSRC = ConstMap.make(map);
                        }
                        final String tempcode = tempdir + File.separatorChar + i + ".als"; //colorful Alloy
                        final String tempXML = tempdir + File.separatorChar + i + ".cnf.xml";
                        final String tempCNF = tempdir + File.separatorChar + i + ".cnf";
                        final Command cmd = cmds.get(i);
                        rep.tempfile = tempCNF;
                        cb(out, "bold", "Executing \"" + cmd + "\"\n");

//----------------------------------------------colorful Alloy---------------------------------------------------------------

                        A4Solution ai;
                        long startTime = System.currentTimeMillis();
                        StringBuilder print = new StringBuilder();
                        if (cmd != null ) {
                            if(cmd.feats == null){
                                expressionProject.executefeats = new HashSet<>();
                                printAmalgamatedModule(print, world, cmd, allFeats);

                            }else {

                                //expressionProject.executefeats = new HashSet<>(cmd.feats.feats);
                                //exactly
                                if (cmd.feats.isExact) {
                                    if(!cmd.feats.feats.isEmpty())
                                        //executefeats contains no Negative features
                                        expressionProject.executefeats = new HashSet<>(addExecuteFeats(cmd.feats.feats,allFeats));
                                    else
                                        expressionProject.executefeats=new HashSet<>();
                                    expressionProject reconstructExpr = new expressionProject();
                                    generateModule(print, world, reconstructExpr, cmd, allFeats);

                                    //amalgatmate
                                } else {
                                    //executefeats contains Negative Features
                                    expressionProject.executefeats = new HashSet<>(cmd.feats.feats);
                                    printAmalgamatedModule(print, world, cmd, allFeats);
                                }
                            }
                        }
                        getexecutecodeTime=System.currentTimeMillis() - startTime;
                        File Nmodule = new File(tempcode);
                        String output = Nmodule.getAbsolutePath();

                        if (print != null)
                            Util.writeAll(output, print.toString());
                        long afterprinttime = System.currentTimeMillis();

                        Module worldNewExecute = CompUtil.parseEverything_fromFile(rep, null, output);
                        parserTime=System.currentTimeMillis()-afterprinttime;

                        ai = TranslateAlloyToKodkod.execute_commandFromBook(rep, worldNewExecute.getAllReachableSigs(), worldNewExecute.getAllCommands().get(0), options);

//----------------------------------------------colorful Alloy---------------------------------------------------------------

                        if (ai == null)
                            result.add(null);
                        else if (ai.satisfiable())
                            result.add(tempXML);

                        else if (ai.highLevelCore().a.size() > 0)
                            result.add(tempCNF + ".core");
                        else result.add("");
                    }



            (new File(tempdir)).delete(); // In case it was UNSAT, or
                                         // canceled...
            if (result.size() > 1) {
                rep.cb("bold", "" + result.size() + " commands were executed. The results are:\n");
                for (int i = 0; i < result.size(); i++) {
                    Command r = world.getAllCommands().get(i);
                    if (result.get(i) == null) {
                        rep.cb("", "   #" + (i + 1) + ": Unknown.\n");
                        continue;
                    }
                    if (result.get(i).endsWith(".xml")) {
                        rep.cb("", "   #" + (i + 1) + ": ");
                        rep.cb("link", r.check ? "Counterexample found. " : "Instance found. ", "XML: " + result.get(i));
                        rep.cb("", r.label + (r.check ? " is invalid" : " is consistent"));
                        if (r.expects == 0)
                            rep.cb("", ", contrary to expectation");
                        else if (r.expects == 1)
                            rep.cb("", ", as expected");
                    } else if (result.get(i).endsWith(".core")) {
                        rep.cb("", "   #" + (i + 1) + ": ");
                        rep.cb("link", r.check ? "No counterexample found. " : "No instance found. ", "CORE: " + result.get(i));
                        rep.cb("", r.label + (r.check ? " may be valid" : " may be inconsistent"));
                        if (r.expects == 1)
                            rep.cb("", ", contrary to expectation");
                        else if (r.expects == 0)
                            rep.cb("", ", as expected");
                    } else {
                        if (r.check)
                            rep.cb("", "   #" + (i + 1) + ": No counterexample found. " + r.label + " may be valid");
                        else
                            rep.cb("", "   #" + (i + 1) + ": No instance found. " + r.label + " may be inconsistent");
                        if (r.expects == 1)
                            rep.cb("", ", contrary to expectation");
                        else if (r.expects == 0)
                            rep.cb("", ", as expected");
                    }
                    rep.cb("", ".\n");
                }
                rep.cb("", "\n");
            }
            if (rep.warn > 1)
                rep.cb("bold", "Note: There were " + rep.warn + " compilation warnings. Please scroll up to see them.\n");
            if (rep.warn == 1)
                rep.cb("bold", "Note: There was 1 compilation warning. Please scroll up to see it.\n");
        }

        private Set<Integer> addExecuteFeats(List<Integer> feats, Set<Integer> allFeats) {
            Set<Integer> commandfeats=new HashSet<>();
            Set<Integer> remain=new HashSet<>();
            for (Integer i: allFeats){
                remain.add(i>0?i: -i);
            }

            for(Integer i: feats){
                if(i>0)
                    commandfeats.add(i);
                else
                    remain.remove(-i);
            }
            if(commandfeats.isEmpty())
                commandfeats=remain;
            else{
                commandfeats.retainAll(remain);
            }
            return commandfeats;
        }

        //colorful Alloy
        /**
         * generate code for amalgamated method
         * @param print used to store the generated code
         * @param world original module(before print)
         * @param cmd executed Command
         * @param allFeats features present in the original module
         */
        public void printAmalgamatedModule(StringBuilder print, Module world, Command cmd,Set<Integer> allFeats){

            checkexecutedfeats(allFeats,cmd.feats);
            AmalgamatedExprPrinterVisitor printAmalgamatedExpr=new AmalgamatedExprPrinterVisitor();
            ExprPrinterVisitor printExprs=new ExprPrinterVisitor();

            //print module keyword
            if(!world.getModelName().equals("unknown")){
                print.append("module "+world.getModelName()+"\r\n\r\n");
            }

            //print opens
            printOpenLine((CompModule)world,print);
            print.append("\r\n");

            addAuxiliarySignatures(allFeats,print);

            printAmalgamatedSigs(print,world,printExprs,printAmalgamatedExpr);

            printAmalgamatedfact(print,world,printAmalgamatedExpr);

            printAmalgamatedfuns(print,world,printAmalgamatedExpr);

            printAmalgamatedAssert(print,world,printAmalgamatedExpr);

            if(cmd!=null)
                printAmalgamatedCommand(print,world,cmd,printAmalgamatedExpr,allFeats);
        }

        //colorful Alloy
        /**
         * convinent method, help to print the amalgamated executed command and feature selected facts.
         *
         * @param print used to store the generated code
         * @param world original module(before print)
         * @param cmd   executed Command
         * @param printAmalgamatedExpr  Visitor, used to print the amalgamated expression
         */
        private void printAmalgamatedCommand(StringBuilder print, Module world,Command cmd, AmalgamatedExprPrinterVisitor printAmalgamatedExpr,Set<Integer>moudulefeats) {

                if(!cmd.label.equals("Default")) {

                    if (cmd.check)
                        print.append("\r\n\r\ncheck ");
                    else print.append("\r\n\r\nrun ");

                    if (cmd.label.startsWith("run$") || cmd.label.startsWith("check$")) {
                        print.append("{");
                        for (Func func : world.getAllFunc()) {
                            if (cmd.label.equals(func.label.substring(5))) {
                                if (!(func.getBody() instanceof ExprConstant))
                                    print.append(func.getBody().accept(printAmalgamatedExpr));
                            }
                        }
                        print.append("}");
                    } else
                        print.append(cmd.label);

                    print.append(" for ");
                    print.append(cmd.overall > 0 ? cmd.overall + " " : 4 + " ");

                    if (cmd.scope.size() >= 1 || cmd.bitwidth != -1)
                        print.append(" but ");
                    if (cmd.bitwidth != -1) {
                        print.append(cmd.bitwidth + " Int ");
                        if(!cmd.scope.isEmpty())
                            print.append(",");
                    }

                    for (CommandScope cs : cmd.scope) {
                        if (cs.isExact)
                            print.append(" exactly ");
                        print.append(cs.startingScope + " ");
                        print.append(cs.sig.label.substring(5) + ",");
                    }

                    print.deleteCharAt(print.length() - 1);

                    if (cmd.expects >= 0)
                        print.append(" expect ").append(cmd.expects);

                    //module with no feature
                    if(!moudulefeats.isEmpty()){
                    print.append(" \r\n\r\nfact selectedFeatures {\r\n        ");
                    if (cmd.feats == null && cmd.feats.feats.isEmpty()) {
                        print.append(" no _Product_");

                    } else {

                        Set<Integer> NFeatures = new HashSet<>();
                        Set<Integer> PFeatures = new HashSet<>();
                        for (Integer i : cmd.feats.feats) {
                            if (i < 0)
                                NFeatures.add(-i);
                            else PFeatures.add(i);
                        }

                        if (!PFeatures.isEmpty()) {
                            if (cmd.feats.feats.contains(1))
                                print.append("_F1+");
                            if (cmd.feats.feats.contains(2))
                                print.append("_F2+");
                            if (cmd.feats.feats.contains(3))
                                print.append("_F3+");
                            if (cmd.feats.feats.contains(4))
                                print.append("_F4+");
                            if (cmd.feats.feats.contains(5))
                                print.append("_F5+");
                            if (cmd.feats.feats.contains(6))
                                print.append("_F6+");
                            if (cmd.feats.feats.contains(7))
                                print.append("_F7+");
                            if (cmd.feats.feats.contains(8))
                                print.append("_F8+");
                            if (cmd.feats.feats.contains(9))
                                print.append("_F9+");

                            print.deleteCharAt(print.length() - 1);
                            print.append(" in _Product_  &&");
                        }

                        if (!NFeatures.isEmpty()) {
                            if (cmd.feats.feats.contains(-1))
                                print.append("_F1 not in _Product_ &&");
                            if (cmd.feats.feats.contains(-2))
                                print.append("_F2 not in _Product_ &&");
                            if (cmd.feats.feats.contains(-3))
                                print.append("_F3 not in _Product_ &&");
                            if (cmd.feats.feats.contains(-4))
                                print.append("_F4 not in _Product_ &&");
                            if (cmd.feats.feats.contains(-5))
                                print.append("_F5 not in _Product_ &&");
                            if (cmd.feats.feats.contains(-6))
                                print.append("_F6 not in _Product_ &&");
                            if (cmd.feats.feats.contains(-7))
                                print.append("_F7 not in _Product_ &&");
                            if (cmd.feats.feats.contains(-8))
                                print.append("_F8 not in _Product_ &&");
                            if (cmd.feats.feats.contains(9))
                                print.append("_F9 not in _Product_ &&");
                        }
                        print.deleteCharAt(print.length() - 1);
                        print.deleteCharAt(print.length() - 1);
                        print.append("\r\n        }");
                    }

                }

                }
        }

        //colorful Alloy
        /**
         * convenient method,help to print amalgamated assert
         * @param print used to store the generated code
         * @param world  original module (before print)
         * @param printAmalgamatedExpr Visitor, used to print the amalgamated expression
         */
        private void printAmalgamatedAssert(StringBuilder print, Module world, AmalgamatedExprPrinterVisitor printAmalgamatedExpr) {
            for(Pair<String,Expr> asser:world.getAllAssertions()){
                if(asser.a.startsWith("check$"))
                    continue;

                print.append("\r\n\r\n");
                print.append("assert ");
                print.append(asser.a);

                print.append("{\r\n");

                if((asser.b instanceof ExprUnary) && !(((ExprUnary) asser.b).sub instanceof ExprConstant))
                    print.append("        "+asser.b.accept(printAmalgamatedExpr));
                print.append("\r\n        }");
            }
        }

        //colorful Alloy
        /**
         * convenient method, help to print amalgamated fun and pred
         * @param print used to store the generated code
         * @param world original module(before print)
         * @param printAmalgamatedExpr visitor, used to print the amalgamated expression
         */
        private void printAmalgamatedfuns(StringBuilder print, Module world, AmalgamatedExprPrinterVisitor printAmalgamatedExpr) {

            for(Func func: world.getAllFunc()){

                if(func.label.startsWith("this/run$"))
                    continue;
                if(!(func.label.equals("this/$$Default"))){

                    print.append("\r\n");
                    if (func.isPred )
                        print.append("pred " +func.label.substring(5)+" ");
                    else
                        print.append("fun "+func.label.substring(5)+" ");

                    if(func.decls.size()>0)
                    {
                        print.append("[");
                        for (Decl decl :func.decls){
                            if(decl.disjoint!=null)
                                print.append( " disj "); //"disj" key word

                            for (Expr expr: decl.names){
                                print.append(expr.accept(printAmalgamatedExpr)+",");
                            }
                            print.deleteCharAt(print.length() - 1);
                            print.append(": ");
                            print.append(decl.expr.accept(printAmalgamatedExpr)+",");
                        }
                        print.deleteCharAt(print.length()-1);
                        print.append("]");
                    }


                    if(!func.isPred && !func.returnDecl.equals(ExprConstant.Op.FALSE))
                    {
                        print.append(":");
                        print.append(func.returnDecl.accept(printAmalgamatedExpr));
                    }

                    print.append("{\r\n        ");


                    //filter cases such as pred show{}: pred show{true }
                    if(!(func.getBody() instanceof ExprConstant)) {
                        if (!func.color.isEmpty()) {
                            addFeatureprefix(func.color, print);
                        }

                        print.append(func.getBody().accept(printAmalgamatedExpr));
                    }
                    print.append("\r\n        }\r\n");
                }
            }
        }

        //colorful Alloy
        /**
         * convenient method, help to print amalgamated fact
         * @param print used to store the generated code
         * @param world original module(before print)
         * @param printAmalgamatedExpr visitor, used to print the amalgamated expression
         */
        private void printAmalgamatedfact(StringBuilder print, Module world, AmalgamatedExprPrinterVisitor printAmalgamatedExpr){

            for (Pair<String, Expr> f: world.getAllFacts()){
                print.append("\r\nfact ");
                print.append(f.a.startsWith("fact$")? "{\r\n" : f.a+ "{\r\n");
                String temp=f.b.accept(printAmalgamatedExpr);
                // include the case of "fact{}"
                print.append("        "+(temp.equals(" true ")? "": temp));
                print.append(" \r\n        }\r\n ");
            }
        }

        //colorful Alloy
        /**
         * convenient method, help to print facts of sig
         * @param print
         * @param s sig these facts belongs to
         * @param facts
         * @param printAmalgamatedExpr
         */
        private void printAmalgamatedfact(StringBuilder print, Sig s, SafeList<Expr> facts, AmalgamatedExprPrinterVisitor printAmalgamatedExpr) {
            for (Expr f: facts){
                print.append("{\r\n");
                String temp =f.accept(printAmalgamatedExpr);
                if(s.label.startsWith("this/"))
                    temp=temp.replace(s.label.substring(5)+".","");

                temp=temp.replace("this .","");
                print.append("        "+temp);
                print.append(" \r\n        } ");

            }
        }

        //colorful Alloy
        /**
         * convenient method, help to print amalgamated sigs
         * @param print used to store the generated code
         * @param world original module(before print)
         * @param printExprs visitor, used to print expression
         */
        private void printAmalgamatedSigs(StringBuilder print, Module world, ExprPrinterVisitor printExprs,AmalgamatedExprPrinterVisitor printAmalgamatedExpr) {
            for(int i=0; i<world.getAllSigs().size();i++){
                Sig s =world.getAllSigs().get(i);

                if(s.isAbstract!=null)
                    print.append("abstract ");
                if(s.isLone !=null)
                    print.append("lone ");

                // if painted with features, change to "lone"
                if (s.isOne!=null)
                    print.append( s.color.isEmpty()?"one ":"lone ");

                print.append("sig "+ s.label.substring(5));

                if(s.isSubsig!=null ){
                    if(((Sig.PrimSig) s).parent!=UNIV){
                        print.append(" extends ");
                        print.append( ((Sig.PrimSig) s).parent.label.substring(5));
                    }
                }

                if(s.isSubset!=null){
                    print.append(" in ");

                    //add first parent sig
                    print.append(((Sig.SubsetSig) s).parents.get(0).label.substring(5));
                    // not one parent
                    if(((Sig.SubsetSig) s).parents.size()>1){
                        for (int j=1;j< ((Sig.SubsetSig) s).parents.size()-1;j ++){
                            print.append(" + "+((Sig.SubsetSig) s).parents.get(j).label.substring(5));
                        }
                    }
                }


                //print fields
                print.append("{");

                for (Decl f:s.getFieldDecls()){
                    print.append(f.disjoint!=null? "\r\n        disj ": "\r\n        ");
                    if(f.names.size()>=1){
                        for(ExprHasName n:f.names){
                            print.append(n.label+",");
                        }
                        print.deleteCharAt(print.length()-1);
                        print.append(": ");

                        //get the first Field
                        Sig.Field n= (Sig.Field)f.names.get(0);

                        if(n.decl().expr instanceof ExprUnary)
                        {
                            // one  ----> lone
                            if(((ExprUnary) n.decl().expr).op.equals(ExprUnary.Op.ONEOF)) {
                                print.append( f.color.isEmpty()?"one ":"lone ");
                                print.append( ((ExprUnary) n.decl().expr).sub.accept(printExprs)+",");
                            }
                            // some -----> set
                            else if(((ExprUnary) n.decl().expr).op.equals(ExprUnary.Op.SOMEOF)) {
                                print.append(f.color.isEmpty()? "some ":"set ");
                                print.append( ((ExprUnary) n.decl().expr).sub.accept(printExprs)+",");
                            }
                            else
                                print.append( n.decl().expr.accept(printExprs)+",");

                        }else
                        {

                            if(!f.color.isEmpty())
                            {
                                // one  ----> lone
                                String temp=n.decl().expr.accept(printExprs).replace(" one"," lone");
                                // some ----->
                                String tempn=temp.replace("some","");
                                print.append( tempn+",");
                            }
                            else
                               print.append( n.decl().expr.accept(printExprs)+",");
                        }
                       }
                    }


                if(!s.getFieldDecls().isEmpty()){
                    print.deleteCharAt(print.length()-1);
                    //} of Sig
                    print.append("\r\n        }");
                }else
                //} of Sig
                print.append("}");


                // Add original facts to sig
                printAmalgamatedfact(print,s,s.getFacts(), printAmalgamatedExpr);

                // add feature facts to sig and field  ------------------------------
                addFeatureFact(s, print);
                // facts for Field
                if(s.getFields().size()>0){

                    for (Sig.Field f:s.getFields()){
                        addFeatureFact(f,print);
                    }
                }
                print.append("\r\n");
            }
            print.append("\r\n");
        }

        //colorful Alloy
        /**
         * convenient method, help to print feature facts for painted Sigs
         * @param s Sig that painted with feature
         * @param print used to store the generated code
         */
        private void addFeatureFact(Sig s, StringBuilder print) {

            String label=s.label.substring(5);
            Set<Integer> NFeatures=new HashSet<>();
            Set<Integer> PFeatures=new HashSet<>();
            for(Integer i: s.color){
                if(i<0)
                    NFeatures.add(-i);
                else PFeatures.add(i);
            }
//marked with NF
            if(!NFeatures.isEmpty()){
                print.append("\r\nfact {\r\n        ");

                // implies none
                addFeatureprefix(NFeatures,print,"in","or");

                print.append(" no "+ label);
                if(s.isLone!=null)
                print.append(" else (some  "+label + " or no "+label +")\r\n        }");

                else
                print.append( " else (some " +label +") \r\n        }" );
            }

            if(!PFeatures.isEmpty()){

                print.append("\r\nfact{ \r\n        ");

                if(s.isOne!=null){
                    //F in P implies
                    addFeatureprefix(PFeatures,print,"in","and");
                    print.append(" (some  "+label + ") else no "+label+"\r\n        }");
                }else{
                    addFeatureprefix(PFeatures,print,"not in","and");
                    print.append(" no  "+label +"\r\n        }");
                }

            }
        }

        //colorful Alloy
        /**
         * convenient method, help to print feature facts fot painted Fields
         * @param f Field that painted with features
         * @param print used to store the generated code
         */
        private void addFeatureFact(Sig.Field f, StringBuilder print){
           // AmalgamatedExprPrinterVisitor printUnionModule=new AmalgamatedExprPrinterVisitor();
            ExprPrinterVisitor printUnionModule=new ExprPrinterVisitor();
            Set<Integer> NFeatures=new HashSet<>();
            Set<Integer> PFeatures=new HashSet<>();
            for(Integer i: f.color){
                if(i<0)
                    NFeatures.add(-i);
                else PFeatures.add(i);
            }

            if(NFeatures.size()>0){
                print.append("\r\nfact {\r\n        ");

                // F in P implies
                addFeatureprefix(NFeatures,print,"in","or");
                print.append( " no " + f.label);
                print.append(" else ");

                print.append(f.label+" in " +f.sig.label.substring(5) +" ->");
                print.append(f.decl().expr.accept(printUnionModule));

                print.append("\r\n\r\n        }");
            }

            if(PFeatures.size()>0){

                print.append("\r\nfact {\r\n        ");

                //F in P implies
                addFeatureprefix(PFeatures,print,"in","and");

                print.append( f.label +" in "+ f.sig.label.substring(5)+" ->" );
                print.append(f.decl().expr.accept(printUnionModule));

                print.append( " else no " + f.label);
                print.append("\r\n        }");
            }

        }

        //colorful Alloy
        /**
         * convenient method, help to print the prefix for feature facts (e.g.  "F1 in product implies ..." )
         * @param PFeature set of positive features
         * @param str  used to store the generated code
         * @param inOrNot  "in" for positive features, while "not in " for negative features
         * @param operator "and","or" operator
         */
        private void addFeatureprefix(Set<Integer> PFeature,StringBuilder str, String inOrNot,String operator) {
            if(PFeature.size()>1)
                str.append("(");
            for (Integer i: PFeature){
                str.append(" _F"+i + " "+inOrNot+" _Product_ "+operator);
            }
            if(str.length()>=2){
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                if(operator.equals("and"))
                    str.deleteCharAt(str.length()-1);
            }

            if(PFeature.size()>1)
                str.append(")");
            str.append(" implies ");
        }

        private void addFeatureprefix(Set<Integer> PFeature,StringBuilder str) {
            if(PFeature.size()>1)
                str.append("(");
            for (Integer i: PFeature){
                if(i>0)
                str.append(" _F"+i +  " in _Product_ and");
                else
                    str.append(" _F"+ -i +  " not in _Product_ and");
            }
            if(str.length()>3){
                str.delete(str.length()-4,str.length());
            }

            if(PFeature.size()>1)
                str.append(")");
            str.append(" implies ");
        }

        //colorful Alloy
        /**
         * generate code for iterative method
         * @param print used to store the generated code
         * @param world original module(before print)
         * @param reconstructExpr visitor, used to project feature code
         * @param cmd executed Command
         * @param modulefeats features present in the original module
         */
        public void generateModule(StringBuilder print, Module world, expressionProject reconstructExpr, Command cmd,Set<Integer> modulefeats) {


            checkexecutedfeats(modulefeats,cmd.feats);

            CompModule newModule = new CompModule(null, ((CompModule) world).span().filename, "");

            if(!world.getModelName().equals("unknown")){
                print.append("module "+world.getModelName()+"\r\n\r\n");
            }

            //print opens
            printOpenLine((CompModule)world,print);
            print.append("\r\n");

            addAuxiliarySignatures(modulefeats,print);

            // project sigs------------------------------------------------------------------------------------------
            SafeList<Sig> oldsigs = world.getAllSigs();
            ConstList.TempList<Sig> sigsFinal=projectSigs(reconstructExpr,oldsigs);

            //add sigs to module
            for(Sig s: sigsFinal.makeConst()){
                newModule.sigs.put(s.label,s);
            }
            //used to print expr
            ExprPrinterVisitor printExprs =new ExprPrinterVisitor();


            //print sigs
            printSigs(print,sigsFinal.makeConst(),printExprs);

            // add facts
            SafeList<Pair<String, Expr>> facts = world.getAllFacts();
            for (Pair<String, Expr> f : facts) {
                Expr fact=(f.b).accept(reconstructExpr);
                if(fact==null)
                    continue;
                newModule.addFact(f.b.pos, f.a, fact);
            }

            // print facts
            printFacts(print,newModule,printExprs);

            // add func/pred
            SafeList<Func> funs =world.getAllFunc();
            for(Func fun: funs) {
                fun.getBody().color.addAll(fun.color);
                Expr nbody = (fun.getBody()).accept(reconstructExpr);
                if(nbody==null){
                    newModule.addFunc(fun.pos(),fun.isPrivate,fun.label.substring(5),null,new ArrayList<Decl>(),null,ExprConstant.TRUE);
                    continue;}

                //project decls-------------
                ConstList.TempList<Decl> decls = new ConstList.TempList<Decl>(fun.decls.size());
                for (Decl d : fun.decls) {
                    ConstList.TempList<ExprVar> declsnames = new ConstList.TempList<ExprVar>(fun.decls.size());
                    Expr exp = d.expr.accept(reconstructExpr);
                    if (exp != null) {
                        for (ExprHasName v : d.names) {
                            Expr Exprout = v.accept(reconstructExpr);
                            declsnames.add((ExprVar) Exprout);
                        }
                        if (declsnames.size() != 0) {

                            Decl dd = new Decl(d.isPrivate, d.disjoint, d.disjoint2, declsnames.makeConst(), exp);
                            decls.add(dd);
                        }
                    }
                }

                newModule.addFunc(fun.pos, fun.isPrivate, fun.label.substring(5), null, decls.makeConst(), fun.returnDecl, nbody);

            }
//print func/pred

            printFunc(print,newModule,printExprs);
            printAssert(print, printExprs,reconstructExpr,world,newModule);

//print command ➀
            printCommand(print,world,reconstructExpr,printExprs,cmd,modulefeats);
        }
       // colorful Alloy
        /**
         * used to check if a feature not present in the model is selected in the scope of a command
         * @param modulefeats features present in the model
         * @param feats FeatureScope of the execute command
         * @throws Err
         */
        private void checkexecutedfeats(Set<Integer> modulefeats, FeatureScope feats) throws Err{

            if(feats!=null && ! modulefeats.containsAll(feats.feats)){
                for(Integer feat:feats.feats){
                    if(!modulefeats.contains(feat)&&! modulefeats.contains(-feat)){
                        String fea=getFeature(feat);
                      throw  new ErrorSyntax(feats.pos,"feature "+fea+" not defined");}
                }

            }
        }

        private String getFeature(Integer feat) {
            String feature;
            if(feat.equals(1)||feat.equals(-1))
                feature= "\u2780" ;
            else if(feat.equals(2)||feat.equals(-2))
                feature= "\u2781" ;
            else if(feat.equals(3)||feat.equals(-3))
                feature= "\u2782" ;
            else if(feat.equals(4)||feat.equals(-4))
                feature= "\u2783" ;
            else if(feat.equals(5)||feat.equals(-5))
                feature= "\u2784" ;
            else if(feat.equals(6)||feat.equals(-6))
                feature= "\u2785" ;
            else if(feat.equals(7)||feat.equals(-7))
                feature= "\u2786" ;
            else if(feat.equals(8)||feat.equals(-8))
                feature= "\u2787" ;
            else
                feature="\u2788" ;

            return  feature;
        }

        //colorful Alloy
        /**
         * Add auxiliary signatures for new generated module
         * @param allfeats  features present in the orginal Module
         * @param print  store the generated code
         */
        private void addAuxiliarySignatures(Set<Integer> allfeats, StringBuilder print) {
            if(!allfeats.isEmpty()) {
                print.append("private abstract sig _Feature_{}\r\n");
                print.append("private one sig ");
                for (Integer i : allfeats) {
                    if(i>0)
                        print.append("_F"+i+",");
                    else if(i<0) {
                        if(! allfeats.contains(-i))
                            print.append("_F"+ -i+ ",");
                    }
                }
                print.deleteCharAt(print.length()-1);
                print.append(" extends _Feature_{}\r\n");
                print.append("private sig _Product_ in _Feature_{}\r\n\r\n");
            }
        }

        //colorful Alloy
        /**
         * convenient method, print execute command for iterative metod.
         * @param print store generated code
         * @param world original module
         * @param reconstructExpr used to get project expressions
         * @param printExprs expression print visitor
         * @param cmd current execute command
         * @param modulefeats features in the module,used when painted with negative features,for example, "check{} with ➊ for 3"
         */
        private void printCommand(StringBuilder print, Module world,expressionProject reconstructExpr, ExprPrinterVisitor printExprs,Command cmd ,Set<Integer> modulefeats) throws ErrorSyntax {

            print.append(cmd.check ? "\r\n\r\ncheck " : "\r\nrun ");

            if (cmd.label.startsWith("run$") || cmd.label.startsWith("check$")) {
                print.append("{");
                for (Func runFunc : world.getAllFunc()) {
                    if (cmd.label.equals(runFunc.label.substring(5)))
                        if (!(runFunc.getBody() instanceof ExprConstant)) {
                            if((cmd.feats==null && !runFunc.color.isEmpty())|| (!cmd.feats.feats.containsAll(runFunc.color)))
                                throw new ErrorSyntax(runFunc.pos,"");
                            Expr bodyNew=runFunc.getBody().accept(reconstructExpr);
                            if(bodyNew!=null)
                                print.append(bodyNew.accept(printExprs));
                            break;
                        }
                }
                print.append("}");
            } else
                print.append(cmd.label);


            print.append(" for ");
            print.append(cmd.overall > 0 ? cmd.overall + " " : 4 + " ");

            if (cmd.scope.size() >= 1 || cmd.bitwidth != -1)
                print.append(" but ");
            if (cmd.bitwidth != -1) {
                print.append(cmd.bitwidth + " Int ");
                if(!cmd.scope.isEmpty() )
                    print.append(",");
            }

            for (CommandScope cs : cmd.scope) {

                if (cs.isExact)
                    print.append(" exactly ");
                print.append(cs.startingScope + " ");
                print.append(cs.sig.label.substring(5) + ",");
            }

            print.deleteCharAt(print.length() - 1);

            if (cmd.expects >= 0)
                print.append(" expect ").append(cmd.expects);
            //module with no feature
            if(!modulefeats.isEmpty()){
            print.append(" \r\n\r\nfact selectedFeatures {\r\n        ");
            if (cmd.feats == null || cmd.feats.feats.isEmpty()) {
                print.append("no _Product_");
            }
            //some features are selected
            else {
                Set<Integer> NFeatures = new HashSet<>();
                Set<Integer> PFeatures = new HashSet<>();
                for (Integer i : cmd.feats.feats) {
                    if (i < 0)
                        NFeatures.add(-i);
                    else PFeatures.add(i);
                }
                print.append("_Product_=");
                if (!PFeatures.isEmpty()) {

                    if (cmd.feats.feats.contains(1))
                        print.append("_F1+");
                    if (cmd.feats.feats.contains(2))
                        print.append("_F2+");
                    if (cmd.feats.feats.contains(3))
                        print.append("_F3+");
                    if (cmd.feats.feats.contains(4))
                        print.append("_F4+");
                    if (cmd.feats.feats.contains(5))
                        print.append("_F5+");
                    if (cmd.feats.feats.contains(6))
                        print.append("_F6+");
                    if (cmd.feats.feats.contains(7))
                        print.append("_F7+");
                    if (cmd.feats.feats.contains(8))
                        print.append("_F8+");
                    if (cmd.feats.feats.contains(9))
                        print.append("_F9+");
                }

                if (!NFeatures.isEmpty() && PFeatures.isEmpty()) {
                    Set<Integer> retain = new HashSet<>();
                    for (Integer integer : modulefeats) {
                        retain.add(integer > 0 ? integer : -integer);
                    }
                    retain.removeAll(NFeatures);
                    if (retain.isEmpty())
                        print.append("none ");
                    else
                        for (Integer i : retain) {
                            print.append("_F" + i + "+");
                        }
                }
                print.deleteCharAt(print.length() - 1);
            }
            print.append("\r\n        }");
         }
        }

        //colorful Alloy
        /**
         *convenient method,print assertation for iterative metod.
         * @param print store generated code
         * @param printExprs expression print visitor,used to print expressions after project
         * @param reconstructExpr used to get project expressions
         * @param world original module
         */
        private void printAssert(StringBuilder print, ExprPrinterVisitor printExprs, expressionProject reconstructExpr, Module world,CompModule newModule) {
            for(Pair<String,Expr> asser:world.getAllAssertions()){
                Expr temp=asser.b.accept(reconstructExpr);

                if(temp==null){
                    print.append("\r\nassert "+(asser.a.startsWith("check$")? " {}":asser.a )+" { }");
                    continue;
                }
               // newModule.addAssertion(asser.b.pos,asser.a,temp);
                if(asser.a.startsWith("check$"))
                    continue;

                print.append("\r\n"+"assert "+asser.a+" {\r\n");

                if((temp instanceof ExprUnary) && !(((ExprUnary) temp).sub instanceof ExprConstant))
                    print.append("        "+temp.accept(printExprs));
                print.append("\r\n        }");
            }
        }

        //colorful Alloy
        /**
         * convenient method, project Sigs according the select features
         * @param reconstructExpr ,visitor, used to
         * @param oldsigs  sigs before feature project
         * @return new sigs after feature project
         */
        private ConstList.TempList<Sig> projectSigs(expressionProject reconstructExpr, SafeList<Sig> oldsigs) {
            ConstList.TempList<Sig> sigsFinal=new ConstList.TempList<>();
            // check every sig in the Module
            for (Sig sig : oldsigs) {
                Sig sigTemp = (Sig) sig.accept(reconstructExpr);
                if (sigTemp != null) {

                    SafeList<Expr> sigf = sig.getFacts();

                    //project sig facts
                    for (Expr factExpr : sigf) {
                        //got sigs and fields are point to old sigs and fields
                        Expr temp=factExpr.accept(reconstructExpr);
                        if(temp!=null)
                            sigTemp.addFact(temp);
                    }
                    sigsFinal.add(sigTemp);
                }
            }
            return sigsFinal;
        }

        //colorful Alloy
        /**
         * convinent method,used to print fun and pred for iterative method
         * @param print used to store the generated code
         * @param newModule new module store new facts
         * @param printExprs visitor, used to print Expr
         */
        private void printFunc(StringBuilder print, CompModule newModule, ExprPrinterVisitor printExprs) {
            for(Func f: newModule.getAllFunc()){
                if (f.label.startsWith("run$"))
                    continue;
                if (f.label.startsWith("$$Default"))
                    continue;

                if(f.returnDecl.equals(ExprConstant.FALSE))
                    print.append("pred "+f.label+" ");
                else
                     print.append("fun "+f.label+" ");


                print.append("[");
                for (Decl d : f.decls) {
                    if(d.disjoint!=null)
                        print.append( " disj "); //"disj" key word

                    for (ExprHasName v : d.names) {
                        print.append( v.accept(printExprs)+",");
                    }

                    print.deleteCharAt(print.length()-1);
                    print.append(": "+d.expr.accept(printExprs)+",");
                }
                print.deleteCharAt(print.length()-1);
                if(!f.decls.isEmpty())
                    print.append("]");
//return
                if(!(f.returnDecl.equals(ExprConstant.FALSE))){
                    print.append(":");
                    if(f.returnDecl instanceof Expr)
                        print.append(f.returnDecl.accept(printExprs));
                }


                if(f.getBody() instanceof ExprConstant)
                    print.append("{ }\r\n");
                else{
                    print.append("{ \r\n");
                    print.append("        "+f.getBody().accept(printExprs)+" \r\n        }\r\n");
                }
            }
        }

        //colorful Alloy
        /**
         * convinent method,used to print fact for iterative method
         * @param print used to store the generated code
         * @param newModule new module store new facts
         * @param printExprs visitor, used to print Expr
         */
        private void printFacts(StringBuilder print,Module newModule, ExprPrinterVisitor printExprs) {
            for (Pair<String, Expr> f: newModule.getAllFacts()){
                print.append("\r\nfact ");
                print.append(f.a.startsWith("fact$")?" {\r\n":f.a+ " {\r\n" );
                String temp=f.b.accept(printExprs);
                // include the case of "fact{}"
                print.append("        "+(temp.equals(" true")? "": temp)+"\r\n        }\r\n");

            }
        }

        //colorful Alloy
        /**
         * convinent method,used to print sigs for exactly method
         * @param print used to store the generated code
         * @param sigsFinal used to store project sigs
         * @param printExprs visitor, used to print Field Expr
         */
        private void printSigs(StringBuilder print, ConstList<Sig>sigsFinal, ExprPrinterVisitor printExprs) {
            for(int i=0; i<sigsFinal.size();i++){

                Sig s =sigsFinal.get(i);
                if(s.isAbstract!=null){
                    print.append("abstract ");
                }
                if(s.isLone !=null){
                    print.append("lone ");
                }
                if (s.isOne!=null){
                    print.append("one ");
                }
                if(s.isSome != null){
                    print.append("some ");
                }

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
                    print.append(f.disjoint!=null? "\r\n        disj ": "\r\n        ");
                    if(f.names.size()>=1){
                        for(ExprHasName n:f.names){
                            print.append(n.label+",");
                        }
                        print.deleteCharAt(print.length()-1);
                        print.append(": ");

                        //get the first Field
                        Sig.Field n= (Sig.Field)f.names.get(0);

                            print.append( n.decl().expr.accept(printExprs)+",");
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
                        String temp=fact.accept(printExprs);
                        //replace "s.fileld" to field
                        temp=temp.replace(s.label.substring(5)+" .","");
                        print.append("\r\n        "+temp);
                    }
                    print.append("\r\n        }\r\n");
                }
                print.append("\r\n");
            }


        }

        //colorful Alloy
        /**
         * used to print the code for import module,for example, "open util/ordering[Time]"
         * @param root  original module
         * @param print store the generated code
         */
        private void printOpenLine( CompModule root,StringBuilder print) {

            for (CompModule.Open open:root.getOpens()){

                if(!open.filename.equals("util/integer")){

                    print.append("open "+open.filename+" ");
                    if(open.args.size()!=0){
                        print.append("[");
                        for(String s:open.args) {
                            print.append(s+",");
                        }
                        print.deleteCharAt(print.length()-1);
                        print.append("] \r\n");
                    }
                }

            }
        }
    }
}
