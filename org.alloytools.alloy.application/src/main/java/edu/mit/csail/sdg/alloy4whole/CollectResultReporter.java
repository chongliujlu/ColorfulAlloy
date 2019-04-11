package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.printExpr.expressionProject;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

/**
 * for collecting results
 */
public class CollectResultReporter extends A4Reporter {
    static StringBuilder commandresult= new StringBuilder();



    /**
     * The time that the last action began; we subtract it from
     * System.currentTimeMillis() to determine the elapsed time.
     */
    private long          lastTime  = 0;
    /**
     * If we performed unsat core minimization, then this is the start of the
     * minimization, else this is 0.
     */
    private long          minimized = 0;



    /** {@inheritDoc} */
    @Override
    public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
        lastTime = System.currentTimeMillis();
        //System.out.println("translate start time:"+ lastTime);
    }

    /** {@inheritDoc} */
    @Override
    public void solve(final int primaryVars, final int totalVars, final int clauses) {
        minimized = 0;
        commandresult.append(primaryVars+","+totalVars+","+clauses+","+(System.currentTimeMillis()-lastTime)+",");
       // System.out.println("solve time:"+(System.currentTimeMillis()-lastTime));
       // System.out.println(" PrimaryVars:" +primaryVars);
       // System.out.println(" totalVars:" + totalVars);
        lastTime = System.currentTimeMillis();
        //System.out.println("solver end time:"+lastTime);
    }


    /** {@inheritDoc} */
    @Override
    public void resultSAT(Object command, long solvingTime, Object solution) {

        commandresult.append((System.currentTimeMillis()-lastTime));
       // System.out.println( "resultSAT time="+(System.currentTimeMillis()-lastTime));
    }

    /** {@inheritDoc} */
    @Override
    public void resultUNSAT(Object command, long solvingTime, Object solution) {
        commandresult.append((System.currentTimeMillis()-lastTime));
       // System.out.println( "resultUnSAT time="+(System.currentTimeMillis()-lastTime));
    }

    public static void main(String[] args) throws Err {

        VizGUI viz = null;

        CollectResultReporter rep = new CollectResultReporter();

        for (String filename : args) {
            Module world = CompUtil.parseEverything_fromFile(rep, null, filename);


            SimpleReporter.SimpleTask1 simpleTask1 = new SimpleReporter.SimpleTask1();
            A4Options options = new A4Options();
            options.solver = A4Options.SatSolver.SAT4J;


            //record features in the original module
            Set<Integer> Modulefeats = new HashSet<>();      //colorful Alloy
            Modulefeats.addAll(CompModule.feats);           //colorful Alloy

            // run 50 times per command
            for (int i=0;i<50;i++) {
                commandresult.delete(0,commandresult.length());
                commandresult.append("command,project Time,command parser time,PrimaryVars,totalVars,clauses,solveTime,instancegenerate time \r\n");

                int j=1; //the number of commands to run
                for (Command command : world.getAllCommands()) {

                    //command name
                    commandresult.append(command.toString() + ",");
                    long startTime = System.currentTimeMillis();

                    //used to generate code.
                    StringBuilder print = new StringBuilder();
                    if (command != null && command.feats != null) {

                        expressionProject.runfeatures = new HashSet<>(command.feats.feats);

                        //exactly
                        if (command.feats.isExact) {
                            expressionProject reconstructExpr = new expressionProject();
                            simpleTask1.generateModule(print, world, reconstructExpr, command, Modulefeats);

                            //amalgatmate
                        } else {
                            simpleTask1.printAmalgamatedModule(print, world, command, Modulefeats);
                        }
                        commandresult.append((System.currentTimeMillis() - startTime) + ",");

                    }
                    File Nmodule = new File("generatedCode.als");
                    String output = Nmodule.getAbsolutePath();


                    if (print != null)
                        Util.writeAll(output, print.toString());


                    long afterprinttime = System.currentTimeMillis();
                    Module worldNewExecute = CompUtil.parseEverything_fromFile(rep, null, output);


                    commandresult.append((System.currentTimeMillis() - afterprinttime) + ",");
                    A4Solution ai = TranslateAlloyToKodkod.execute_commandFromBook(rep, worldNewExecute.getAllReachableSigs(), worldNewExecute.getAllCommands().get(0), options);
                    commandresult.append("\r\n");

                    j++;
                }

                File Nmodule = new File("out/data/result"+i+".txt");
                String output = Nmodule.getAbsolutePath();

                if (commandresult != null)
                    Util.writeAll(output, commandresult.toString());
               // System.out.println(commandresult);

            }






        }
    }

}
