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

package edu.mit.csail.sdg.ast;

import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Container;
import java.awt.Font;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.JToolBar;
import javax.swing.ScrollPaneConstants;
import javax.swing.WindowConstants;
import javax.swing.border.EmptyBorder;
import javax.swing.tree.TreePath;

import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Listener;
import edu.mit.csail.sdg.alloy4.Listeners;
import edu.mit.csail.sdg.alloy4.OurAntiAlias;
import edu.mit.csail.sdg.alloy4.OurBorder;
import edu.mit.csail.sdg.alloy4.OurTabbedSyntaxWidget;
import edu.mit.csail.sdg.alloy4.OurTree;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

/**
 * This abstract class represents a node that can be browsed in the graphical
 * parse tree viewer.
 */

public abstract class Browsable {

    // [HASLab] colorful Alloy
    public Set<Integer> color = new HashSet<Integer>();

    // [HASLab] colorful Alloy
    public void paint(int c) {
        color.add(c);
    }

    // [HASLab] colorful Alloy
    public void paint(Collection<Integer> c) {
        color.addAll(c);
    }

    Set<Integer> selectedFeature = new HashSet<>();
    // store new sigs
    Map<Sig,Sig> sigOld2new      = new HashMap<>();
    // Map <Field,Field> field2newField =new HashMap<>();

    JTextArea    textLabel       = new JTextArea();
    JFrame       x;



    /**
     * Returns a Pos object representing the position of this Expr.
     */
    public Pos pos() {
        return Pos.UNKNOWN;
    }

    /**
     * Returns a Pos object representing the entire span of this Expr and all its
     * subexpressions.
     */
    public Pos span() {
        return pos();
    }

    /**
     * Returns the description (as HTML) to show for this node.
     */
    public abstract String getHTML();

    /** Returns a list of subnodes for this node. */
    public abstract List< ? extends Browsable> getSubnodes();

    /**
     * Construct a Browsable node with the given HTML description and the given
     * single subnode.
     */
    public static final Browsable make(final Pos pos, final Pos span, final String html, Browsable subnode) {
        return make(pos, span, html, Util.asList(subnode));
    }

    /**
     * Construct a Browsable node with the given HTML description and the given
     * single subnode.
     */
    public static final Browsable make(final String html, Browsable subnode) {
        return make(Pos.UNKNOWN, Pos.UNKNOWN, html, Util.asList(subnode));
    }

    /**
     * Construct a Browsable node with the given HTML description and the given 0 or
     * more subnodes.
     */
    public static final Browsable make(final String html, final List< ? extends Browsable> subnodes) {
        return make(Pos.UNKNOWN, Pos.UNKNOWN, html, subnodes);
    }

    /**
     * Construct a Browsable node with the given HTML description and the given 0 or
     * more subnodes.
     */
    public static final Browsable make(final Pos pos, final Pos span, final String html, final List< ? extends Browsable> subnodes) {
        final ConstList< ? extends Browsable> constlist = ConstList.make(subnodes);
        return new Browsable() {

            @Override
            public Pos pos() {
                return pos;
            }

            @Override
            public Pos span() {
                return span;
            }

            @Override
            public String getHTML() {
                return html;
            }

            @Override
            public List< ? extends Browsable> getSubnodes() {
                return constlist;
            }
        };
    }

    /**
     * Display this node and its subnodes as a tree; if listener!=null, it will
     * receive OurTree.Event.SELECT events when nodes are selected.
     */
    public final JFrame showAsTree(Listener listener) {
        final OurTree tree = new OurTree(12) {

            private static final long serialVersionUID = 0;
            private final boolean     onWindows        = Util.onWindows();
            {
                do_start();
            }

            @Override
            public String convertValueToText(Object val, boolean selected, boolean expanded, boolean leaf, int row, boolean focus) {
                String c = ">";
                String x = (val instanceof Expr) ? ((Expr) val).toString() : (val instanceof Browsable ? ((Browsable) val).getHTML() : Util.encode(String.valueOf(val)));
                //String x = (val instanceof Browsable) ? ((Browsable) val).getHTML() : Util.encode(String.valueOf(val));
                if (onWindows)
                    c = selected ? " style=\"color:#ffffff;\">" : " style=\"color:#000000;\">";
                return "<html><span" + c + x + "</span></html>";
            }

            @Override
            public List< ? > do_ask(Object parent) {
                if (parent instanceof Browsable)
                    return ((Browsable) parent).getSubnodes();
                else
                    return new ArrayList<Browsable>();
            }

            @Override
            public Object do_root() {
                return Browsable.this;
            }
        };

        /*
         * tree.setBorder(new EmptyBorder(3, 3, 3, 3)); final JScrollPane scr = new
         * JScrollPane(tree, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
         * ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED); scr.addFocusListener(new
         * FocusListener() {
         * @Override public void focusGained(FocusEvent e) {
         * tree.requestFocusInWindow(); }
         * @Override public void focusLost(FocusEvent e) {} }); final JFrame x = new
         * JFrame("Parse Tree"); x.setLayout(new BorderLayout()); x.add(scr,
         * BorderLayout.CENTER); x.pack(); x.setSize(500, 500);
         * x.setLocationRelativeTo(null); x.setVisible(true); if (listener != null)
         * tree.listeners.add(listener); return x;
         */

        CompModule root = (CompModule) tree.getModel().getRoot();

        // fields
        SafeList<Field> fields = new SafeList<>();
        for (Sig sigf : root.getAllSigs()) {
            if (!sigf.getFields().isEmpty())
                fields.addAll(sigf.getFields().makeConstList());
        }


        tree.setEditable(true);
        tree.setBorder(new EmptyBorder(3, 3, 3, 3));
        final JScrollPane scr = new JScrollPane(tree, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        scr.addFocusListener(new FocusListener() {

            @Override
            public void focusGained(FocusEvent e) {
                tree.requestFocusInWindow();
            }

            @Override
            public void focusLost(FocusEvent e) {}
        });

        x = new JFrame("Parse Tree");


        JButton Cancelfeature1 = new JButton("Cancel F1");
        JButton CancelnegFeature1 = new JButton("Cancel NF1");
        JButton Cancelfeature2 = new JButton("Cancel F2");
        JButton CancelnegFeature2 = new JButton("Cancel NF2");
        //layout setting
        JSplitPane verticalPane;
        JPanel topPane;
        JSplitPane bottomPane;

        //feature button
        JButton feature1 = new JButton("F1");
        feature1.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {

                //get selected node in AST tree
                TreePath path = tree.getSelectionPath();
                Object selectedNode = tree.getLastSelectedPathComponent();
                if (selectedNode instanceof Expr) {
                    ((Expr) selectedNode).paint(1);

                    textLabel.setText("\r\n " + ((Expr) selectedNode).toString() + ":  " + ((Expr) selectedNode).color);


                    x.repaint();

                } else if (selectedNode instanceof Browsable &&
                //Field selected
                           (root.find(((Browsable) selectedNode).pos())) instanceof Field) {

                    for (Field f : fields) {
                        if (f.pos.equals(((Browsable) selectedNode).pos())) {
                            f.paint(1);
                            break;
                        }
                    }

                    textLabel.setText("\r\n" + selectedNode.toString() + " : " + ((Browsable) selectedNode).color);

                    x.repaint();
                }

            }
        });

        Cancelfeature1.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {

                Object selectedNode = tree.getLastSelectedPathComponent();
                Browsable newNode = (Browsable) selectedNode;
                newNode.color.remove(1);

                x.repaint();

            }



            /*
             * if (mapExprToFeatures.containsKey(pNode) &&
             * mapExprToFeatures.get(pNode).a.contains(feature1.getText())){
             * textLabel.setText(" Can not cancel F1, Please cancel parent node first!");
             * x.repaint(); }else if (mapExprToFeatures.containsKey(newNode) &&
             * mapExprToFeatures.get(newNode).a.contains(feature1.getText())){
             * mapExprToFeatures.get(newNode).a.remove(feature1.getText()); //send Event to
             * text editor for cancel painting (mark the corresponding color to Expr)
             * listeners.add(listener); listeners.fire(Cancelfeature1, Listener.Event.CLICK,
             * path.getLastPathComponent()); } else { textLabel.setText(" F1 not marked!");
             * x.repaint(); }
             */



        });


        JButton negFeature1 = new JButton("NegaFeature 1");
        negFeature1.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                Object selectedNode = tree.getLastSelectedPathComponent();
                if (selectedNode instanceof Expr) {
                    ((Expr) selectedNode).paint(-1);

                    x.repaint();
                } else if (selectedNode instanceof Browsable &&
                //Field selected
                           (root.find(((Browsable) selectedNode).pos())) instanceof Field) {
                    for (Field f : fields) {
                        if (f.pos.equals(((Browsable) selectedNode).pos())) {
                            f.paint(-1);
                            break;
                        }

                    }
                    x.repaint();
                }
            }
        });



        //feature button
        JButton feature2 = new JButton("F2");
        feature2.addActionListener(new ActionListener() {

            Listeners listeners = new Listeners();

            @Override
            public void actionPerformed(ActionEvent e) {
                Object selectedNode = tree.getLastSelectedPathComponent();

                if (selectedNode instanceof Expr) {
                    ((Expr) selectedNode).paint(2);
                } else if (selectedNode instanceof Browsable &&
                //Field selected
                           (root.find(((Browsable) selectedNode).pos())) instanceof Field) {
                    for (Field f : fields) {
                        if (f.pos.equals(((Browsable) selectedNode).pos())) {
                            f.paint(2);
                            break;
                        }

                    }
                }

                textLabel.setText("\r\n" + "  :" + selectedNode.toString() + " : " + ((Browsable) selectedNode).color);
                x.repaint();
            }
        });

        Cancelfeature2.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {

                TreePath path = tree.getSelectionPath();
                Object selectedNode = tree.getLastSelectedPathComponent();

                TreePath parent = path.getParentPath();

                Object patrentNode = parent.getLastPathComponent();
                ((Browsable) selectedNode).color.remove(2);


                /*
                 * if (mapExprToFeatures.containsKey(pNode) &&
                 * mapExprToFeatures.get(pNode).a.contains(feature2.getText())){
                 * textLabel.setText(" Can not cancel F1, Please cancel parent node first!");
                 * x.repaint(); }else if (mapExprToFeatures.containsKey(newNode) &&
                 * mapExprToFeatures.get(newNode).a.contains(feature2.getText())){
                 * mapExprToFeatures.get(newNode).a.remove(feature2.getText()); //send Event to
                 * text editor for cancel painting (mark the corresponding color to Expr)
                 * listeners.add(listener); listeners.fire(Cancelfeature2, Listener.Event.CLICK,
                 * path.getLastPathComponent()); } else {
                 * textLabel.setText(" NF1 not marked,do not need cancel!"); x.repaint(); }
                 */

            }
        });

        JButton negFeature2 = new JButton("NegaFeature 2");
        negFeature2.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {

                Object selectedNode = tree.getLastSelectedPathComponent();

                Browsable newNode = (Browsable) selectedNode;
                if (selectedNode instanceof Expr) {
                    ((Expr) selectedNode).paint(-2);
                } else if (selectedNode instanceof Browsable &&
                //Field selected
                           (root.find(((Browsable) selectedNode).pos())) instanceof Field) {

                    for (Field f : fields) {
                        if (f.pos.equals(((Browsable) selectedNode).pos())) {
                            f.paint(-2);
                            break;
                        }

                    }
                }

                textLabel.setText("\r\n" + selectedNode.toString() + " :" + newNode.color);
                x.repaint();
            }
        });


        CancelnegFeature2.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {

                TreePath path = tree.getSelectionPath();
                Object selectedNode = tree.getLastSelectedPathComponent();

                ((Browsable) selectedNode).color.remove(-2);
            }
        });


        verticalPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);


        //settings for topPane
        topPane = new JPanel();
        // topPane.setBackground(Color.BLUE);
        JPanel topLeftPane = new JPanel();
        JLabel leftLabel = new JLabel("Add Feature");
        JPanel topLeftAddF = new JPanel();

        topLeftPane.add(leftLabel);
        topLeftPane.add(topLeftAddF);


        GridLayout gridLayout = new GridLayout(2, 4, 3, 3);
        // GridLayout gridLayoutY = new GridLayout(2,1,3,3);
        topLeftAddF.setLayout(gridLayout);
        topLeftAddF.add(feature1);
        topLeftAddF.add(negFeature1);
        topLeftAddF.add(feature2);
        topLeftAddF.add(negFeature2);


        topLeftAddF.add(Cancelfeature1);
        topLeftAddF.add(CancelnegFeature1);
        topLeftAddF.add(Cancelfeature2);
        topLeftAddF.add(CancelnegFeature2);

        BoxLayout leftBoxLayout = new BoxLayout(topLeftPane, BoxLayout.Y_AXIS);
        topLeftPane.setLayout(leftBoxLayout);
        JPanel topRightPane = new JPanel();



        BoxLayout rightBoxLayout = new BoxLayout(topRightPane, BoxLayout.Y_AXIS);
        JLabel rightLabel = new JLabel("Select Features");
        topRightPane.add(rightLabel);
        //topRightPane.setBackground(Color.red);
        topRightPane.setLayout(rightBoxLayout);


        topPane.add(topLeftPane);
        topPane.add(topRightPane);



        Object[] value = new Integer[] {
                                        1, 2, 3, 4, 5, 6, 7, 8, 9, 0
        };
        Object[] defaultValue = new Integer[] {
                                               1, 2, 3, 4, 5, 6, 7, 8, 9,
        };

        MultiComboBox mulit = new MultiComboBox(value, defaultValue);

        mulit.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                //cancel do nothing
                if (e.getActionCommand().equals(MultiPopup.CANCEL_EVENT)) {}
                // all in one Module
                else if (e.getActionCommand().equals(MultiPopup.UnionModule_Event)) {

                    printUnionModule printUnionModule = new printUnionModule();
                    printExpr printExprs = new printExpr();

                    /// generate product
                    StringBuilder print = new StringBuilder();
                    print.append("abstract sig Feature{}\r\n");
                    print.append("sig F1,F2,F3,F4,F5,F6,F7,F8,F9,F0 extends Feature{}\r\n");

                    print.append("sig Product in Feature{}\r\n\r\n");

                    // print sig ------------------------------------------------------
                    for (int i = 0; i < root.sigs.size(); i++) {
                        Sig s = root.getAllSigs().get(i);

                        if (s.isAbstract != null)
                            print.append("abstract ");
                        if (s.isLone != null)
                            print.append("lone ");
                        // change to lone
                        if (s.isOne != null)
                            print.append("lone ");
                        //change to set
                        //if(s.isSome != null)
                        //  print.append(" ");

                        print.append("sig " + s.label.substring(5));


                        if (s.isSubsig != null) {
                            if (((Sig.PrimSig) s).parent != UNIV) {
                                print.append(" extends ");
                                print.append(((Sig.PrimSig) s).parent.label.substring(5));
                            }
                        }

                        if (s.isSubset != null) {
                            print.append(" in ");

                            //add first parent sig
                            print.append(((Sig.SubsetSig) s).parents.get(0).label.substring(5));
                            // not one parent
                            if (((Sig.SubsetSig) s).parents.size() > 1) {
                                for (int j = 1; j < ((Sig.SubsetSig) s).parents.size() - 1; j++) {
                                    print.append(" + " + ((Sig.SubsetSig) s).parents.get(j).label.substring(5));
                                }
                            }
                        }


                        //print fields
                        print.append(" { ");
                        if (s.getFields().size() > 0) {

                            for (Sig.Field f : s.getFields()) {
                                print.append("\r\n   " + f.label + " : ");

                                if (f.decl().expr instanceof ExprUnary) {
                                    // one  ----> lone
                                    if (((ExprUnary) f.decl().expr).op.equals(ExprUnary.Op.ONEOF)) {
                                        print.append("lone ");
                                        print.append(((ExprUnary) f.decl().expr).sub.accept(printExprs) + ",");
                                    }
                                    // some -----> set
                                    else if (((ExprUnary) f.decl().expr).op.equals(ExprUnary.Op.SOMEOF)) {
                                        print.append("set ");
                                        print.append(((ExprUnary) f.decl().expr).sub.accept(printExprs) + ",");
                                    } else {
                                        print.append(f.decl().expr.accept(printExprs) + ",");
                                    }

                                } else
                                    print.append(f.decl().expr.accept(printExprs) + ",");
                            }
                        }

                        print.deleteCharAt(print.length() - 1);

                        //} of Sig
                        print.append("\r\n }\r\n");
                        // add feature facts to sig and field  ------------------------------
                        addFeatureFact(s, print);
                        // facts for Field
                        if (s.getFields().size() > 0) {

                            for (Sig.Field f : s.getFields()) {

                                addFeatureFact(f, print);
                            }
                        }
                        print.append("\r\n\r\n");
                    }



                    //print facts
                    //----------------------------------------------------------------
                    for (Pair<String,Expr> f : root.getAllFacts()) {

                        print.append("\r\nfact ");
                        if (f.a.startsWith("fact$")) {
                            print.append(" {\r\n");

                        } else {
                            print.append("  " + f.a + " {\r\n");
                        }
                        print.append("    " + f.b.accept(printUnionModule));
                        print.append(" }\r\n ");
                    }

                    //  print funs------------------------------------------------------

                    for (Func func : root.getAllFunc()) {

                        if (!(func.label.equals("this/$$Default"))) {

                            print.append("\r\n");
                            if (func.isPred)
                                print.append("pred " + func.label.substring(5) + " ");
                            else
                                print.append("fun " + func.label.substring(5) + " ");

                            if (func.decls.size() > 0) {
                                print.append("[");
                                for (Decl decl : func.decls) {

                                    for (Expr expr : decl.names) {
                                        print.append(expr.accept(printUnionModule) + " ,");
                                    }
                                    print.deleteCharAt(print.length() - 1);
                                    print.append(": ");
                                    print.append(decl.expr.accept(printUnionModule) + ",");
                                }
                                print.deleteCharAt(print.length() - 1);
                                print.append("]");
                            }


                            if (!func.isPred && !func.returnDecl.equals(ExprConstant.Op.FALSE)) {
                                print.append(":");
                                print.append(func.returnDecl.accept(printUnionModule));
                            }

                            print.append("{\r\n  ");
                            print.append(func.getBody().accept(printUnionModule));
                            print.append("\r\n}");
                        }
                    }

                    // print assert-----------------------------------------------------------------
                    for (Pair<String,Expr> asser : root.getAllAssertions()) {
                        print.append("\r\n  ");

                        print.append("assert  ");
                        if (!asser.a.contains("assert$"))
                            print.append(asser.a);
                        print.append("{\r\n");

                        print.append(asser.b.accept(printUnionModule));

                        print.append("\r\n}");

                    }

                    //print run /check----------------------------------------------------------------

                    for (Command command : root.getAllCommands()) {

                        if (!command.label.equals("Default")) {

                            if (command.check)
                                print.append("\r\n check ");
                            else
                                print.append("\r\n run ");

                            print.append(command.label + " " + " for " + command.overall);

                            if (command.scope.size() == 1)
                                print.append(" but ");
                            for (CommandScope cs : command.scope) {
                                if (cs.isExact)
                                    print.append(" exactly ");
                                print.append(cs.startingScope + " ");
                                print.append(cs.sig.label.substring(5) + ",");
                            }

                            print.deleteCharAt(print.length() - 1);
                        }
                    }

                    System.out.println(print);



                    final JFrame frame = new JFrame("Alloy Analyzer");
                    frame.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

                    frame.pack();

                    frame.setSize(600, 600);
                    frame.setLocation(300, 300);
                    frame.setVisible(true);
                    frame.setTitle("Feature  " + selectedFeature + " Selected");

                    //frame.addWindowListener(SimpleGUI.doQuit());
                    JToolBar toolbar;
                    JButton runbutton, stopbutton, showbutton;
                    JScrollPane logpane;
                    OurTabbedSyntaxWidget text = new OurTabbedSyntaxWidget("", 12, A4Preferences.TabSize.get());
                    ;

                    JSplitPane splitpane;



                    JLabel status;
                    Color background = new Color(0.9f, 0.9f, 0.9f);
                    JButton execute = new JButton("Execute");
                    try {

                        toolbar = new JToolBar();
                        toolbar.setFloatable(false);
                        if (!Util.onMac())
                            toolbar.setBackground(background);

                        toolbar.add(execute);



                        // toolbar.add(OurUtil.button("New", "Starts a new blank model", "images/24_new.gif", doNew()));
                        // toolbar.add(OurUtil.button("Open", "Opens an existing model", "images/24_open.gif", doOpen()));
                        // toolbar.add(OurUtil.button("Reload", "Reload all the models from disk", "images/24_reload.gif", doReloadAll()));
                        // toolbar.add(OurUtil.button("Save", "Saves the current model", "images/24_save.gif", doSave()));
                        // toolbar.add(runbutton = OurUtil.button("Execute", "Executes the latest command", "images/24_execute.gif", doExecuteLatest()));
                        // toolbar.add(stopbutton = OurUtil.button("Stop", "Stops the current analysis", "images/24_execute_abort2.gif", doStop(2)));
                        //stopbutton.setVisible(false);
                        //toolbar.add(showbutton = OurUtil.button("Show", "Shows the latest instance", "images/24_graph.gif", doShowLatest()));
                        toolbar.add(Box.createHorizontalGlue());
                        toolbar.setBorder(new OurBorder(false, false, false, false));
                    } finally {

                    }

                    //  OurAntiAlias.enableAntiAlias(AntiAlias.get());

                    // Create the message area
                    logpane = OurUtil.scrollpane(null);
                    //log = new SwingLogPanel(logpane, "宋体", 12, Color.white, Color.BLACK, new Color(.7f, .2f, .2f), this);

                    // Create loggers for preference changes
                    // PreferencesDialog.logOnChange(log, A4Preferences.allUserPrefs().toArray(new A4Preferences.Pref< ? >[0]));

                    // Create the text area

                    //text.listeners.add();
                    text.enableSyntax(true);

                    // Add everything to the frame, then display the frame
                    Container all = frame.getContentPane();
                    all.setLayout(new BorderLayout());
                    all.removeAll();
                    JPanel lefthalf = new JPanel();
                    lefthalf.setLayout(new BorderLayout());
                    lefthalf.add(toolbar, BorderLayout.NORTH);
                    text.addTo(lefthalf, BorderLayout.CENTER);
                    splitpane = OurUtil.splitpane(JSplitPane.HORIZONTAL_SPLIT, lefthalf, logpane, 200);
                    splitpane.setResizeWeight(0.5D);
                    status = OurUtil.make(OurAntiAlias.label(" "), new Font("Times new Rome", Font.PLAIN, 12), Color.BLACK, background);
                    status.setBorder(new OurBorder(true, false, false, false));
                    all.add(splitpane, BorderLayout.CENTER);
                    all.add(status, BorderLayout.SOUTH);

                    text.get().setText(print.toString());

                }
                //execute model with selected features
                else if (e.getActionCommand().equals(MultiPopup.Executed_EVENT)) {

                    reconstructAST reconstructExpr = new reconstructAST();

                    // get selected  features
                    Object[] defaultValues = mulit.popup.getSelectedValues();
                    Set<Integer> Feature = new HashSet();
                    for (Object s : defaultValues) {
                        Feature.add(Integer.valueOf(s.toString()));
                    }
                    selectedFeature = Feature;

                    VizGUI viz = null;

                    A4Reporter rep = new A4Reporter() {

                        // For example, here we choose to display each "warning" by printing
                        // it to System.out
                        @Override
                        public void warning(ErrorWarning msg) {
                            System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                            System.out.flush();
                        }
                    };
                    A4Options options = new A4Options();

                    options.solver = A4Options.SatSolver.SAT4J;

                    // use old sigs and all expr point to original sigs, if I change to new sigs, need change the type of every Field(all sigs in ProductType),
                    // type of every ExprVar,ExprLet, Type in Declations, command socpe, every sig in the bottom of every Expr must point to the new sig (consistency ,can not generate a new sig)
                    for (Command commandn : root.getAllCommands()) {
                        //  Pos pos, Expr e, String label, boolean check, int overall, int bitwidth, int maxseq, int expects, Iterable<CommandScope> scope, Iterable<Sig> additionalExactSig, Expr formula, Command parent)
                        Command command = new Command(commandn.check, commandn.overall, commandn.bitwidth, commandn.maxseq, commandn.formula);
                        // Execute the command
                        System.out.println("============ Command " + ": ============");
                        Expr fom = command.formula;

                        // project run formular
                        Expr exprout = fom.accept(reconstructExpr);
                        exprout.errors.clear();
                        System.out.println(exprout);



                        //change formular
                        Command commandNew = command.change(exprout);
                        /*
                         * //change scope ConstList.TempList<CommandScope> commandscope = new
                         * ConstList.TempList<>(command.scope.size()); for (CommandScope cs :
                         * command.scope) { if (sigOld2new.containsKey(cs.sig) && sigOld2new.get(cs.sig)
                         * != null) { cs.sig = sigOld2new.get(cs.sig); } commandscope.add(cs); }
                         * commandNew = commandNew.change(commandscope.makeConst()); Command parent =
                         * command.parent; if (CommandOld2new.containsKey(command) &&
                         * CommandOld2new.get(command) != null) { parent = CommandOld2new.get(command);
                         * }
                         */

                        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, root.getAllSigs(), commandNew, options);
                        // Print the outcome
                        System.out.println(ans);
                        // If satisfiable...
                        if (ans.satisfiable()) {

                            ans.writeXML("alloy_example_output.xml");
                            //
                            // You can then visualize the XML file by calling this:
                            if (viz == null) {
                                viz = new VizGUI(false, "alloy_example_output.xml", null);
                            } else {
                                viz.loadXML("alloy_example_output.xml", true);
                            }
                        }
                    }
                }

                //generate code based on selected features
                //gengrate new Module (change the type and point sigs?)
                else if (e.getActionCommand().equals(MultiPopup.PROJECT_FEATURE_EVENT)) {

                    // get selected  features
                    Object[] defaultValues = mulit.popup.getSelectedValues();
                    Set<Integer> Feature = new HashSet();
                    for (Object s : defaultValues) {
                        Feature.add(Integer.valueOf(s.toString()));
                    }
                    selectedFeature = Feature;



                    //construct  new AST tree
                    CompModule newModule = new CompModule(null, root.span().filename, "");

                    // project sigs--------------------------------------------------------------------------------------------------------
                    reconstructSigs reconstructsigs = new reconstructSigs();
                    reconstructAST reconstructExpr = new reconstructAST();
                    //get sigs
                    SafeList<Sig> oldsigs = root.getAllSigs();

                    ConstList.TempList<Sig> sigsFinal = new ConstList.TempList<Sig>(oldsigs.size());
                    // check every sig in the Module
                    for (Sig sig : oldsigs) {
                        Sig sigTemp = (Sig) sig.accept(reconstructsigs);
                        SafeList<Expr> sigf = sig.getFacts();

                        //project sig facts
                        for (Expr factExpr : sigf) {
                            //got sigs and fields are point to old sigs and fields
                            sigTemp.addFact(factExpr.accept(reconstructExpr));
                        }

                        sigsFinal.add(sigTemp);


                        sigOld2new.put(sig, sigTemp);
                    }

                    // changeTypepOfField(sigsFinal);

                    //add sigs to module
                    for (Sig s : sigsFinal.makeConst()) {
                        newModule.sigs.put(s.label, s);
                    }
                    //used to print expr
                    printExpr printExprs = new printExpr();

                    StringBuilder print = new StringBuilder();

                    //print opens
                    printOpenLine(print);
                    //print sigs
                    printSigs(print, sigsFinal.makeConst(), printExprs);

                    // add facts
                    SafeList<Pair<String,Expr>> facts = root.getAllFacts();
                    for (Pair<String,Expr> f : facts) {
                        newModule.addFact(f.b.pos, f.a, (f.b).accept(reconstructExpr));
                    }
                    // print facts
                    printFacts(newModule, print, printExprs);

                    // add func/pred
                    SafeList<Func> funs = root.getAllFunc();

                    for (Func fun : funs) {
                        Expr nbody = (fun.getBody()).accept(reconstructExpr);
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
                    printFunc(print, newModule, printExprs);

                    System.out.println(print);

                }
            }

            private void printOpenLine(StringBuilder print) {

                for (CompModule.Open open : root.getOpens()) {


                    if (!open.filename.equals("util/integer")) {

                        print.append("open " + open.filename + " ");
                        if (open.args.size() != 0) {
                            print.append("[");
                            for (String s : open.args) {
                                print.append(s + ",");
                            }
                            print.deleteCharAt(print.length() - 1);
                            print.append("] \r\n");
                        }
                    }

                }
            }
        });

        topRightPane.add(mulit);



        //settings for bottomPane
        bottomPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        JScrollPane right = new JScrollPane();
        //right.setBackground(Color.ORANGE);
        JPanel r = new JPanel();


        right.getViewport().add(textLabel);

        textLabel.setLineWrap(true);
        textLabel.setWrapStyleWord(true);

        bottomPane.setLeftComponent(scr);
        bottomPane.setDividerLocation(450);
        bottomPane.setRightComponent(right);

        // bottomPane.setBackground(Color.green);


        verticalPane.setTopComponent(topPane);
        verticalPane.setBottomComponent(bottomPane);

        x.setLayout(new BorderLayout());
        // x.add(scr, BorderLayout.CENTER);

        x.add(verticalPane);


        x.pack();
        x.setSize(900, 600);
        x.setLocationRelativeTo(null);
        x.setVisible(true);
        if (listener != null)
            tree.listeners.add(listener);
        return x;
    }



    private void addFeatureFact(Sig s, StringBuilder print) {

        String label = s.label.substring(5);
        Set<Integer> NFeatures = new HashSet<>();
        Set<Integer> PFeatures = new HashSet<>();
        for (Integer i : s.color) {
            if (i < 0)
                NFeatures.add(-i);
            else
                PFeatures.add(i);
        }
        //marked with NF
        if (!NFeatures.isEmpty()) {
            print.append("\r\n fact { \r\n ");

            // implies none
            addFeatureprefix(NFeatures, print, "in", "or");

            print.append(" no " + label);

            print.append(" else (some " + label + " or no " + label + ") \r\n}");
        }

        if (!PFeatures.isEmpty()) {

            print.append(" } \r\n fact { \r\n ");

            //F in P implies
            addFeatureprefix(PFeatures, print, "in", "and");

            print.append(" (some  " + label + "  or no " + label + ") else no " + label + "\r\n}");
        }
    }

    private void addFeatureFact(Field f, StringBuilder print) {
        printUnionModule printUnionModule = new printUnionModule();
        Set<Integer> NFeatures = new HashSet<>();
        Set<Integer> PFeatures = new HashSet<>();
        for (Integer i : f.color) {
            if (i < 0)
                NFeatures.add(-i);
            else
                PFeatures.add(i);
        }

        if (NFeatures.size() > 0) {
            print.append("\r\nfact { \r\n ");
            print.append("  ");

            // F in P implies
            addFeatureprefix(NFeatures, print, "in", "or");
            print.append(" no " + f.label);
            print.append(" else ");

            print.append(f.label + " in " + f.sig.label.substring(5) + " ->");
            print.append(f.decl().expr.accept(printUnionModule));

            print.append("\r\n }");
        }

        if (PFeatures.size() > 0) {

            print.append("\r\n fact { \r\n ");

            //F in P implies
            print.append("  ");
            addFeatureprefix(PFeatures, print, "in", "and");

            print.append(f.label + " in " + f.sig.label.substring(5) + " ->");
            print.append(f.decl().expr.accept(printUnionModule));

            print.append(" else no " + f.label);
            print.append("\r\n }");
        }
    }


    private void printFunc(StringBuilder print, CompModule newModule, printExpr printExprs) {
        for (Func f : newModule.getAllFunc()) {
            if (!(f.label.equals("$$Default"))) {

                if (f.returnDecl.equals(ExprConstant.FALSE)) {
                    print.append("pred " + f.label + " ");
                } else {
                    print.append("fun " + f.label + " ");

                }

                print.append("[");
                for (Decl d : f.decls) {

                    for (ExprHasName v : d.names) {
                        print.append(v.accept(printExprs) + ",");
                    }
                    print.deleteCharAt(print.length() - 1);

                    print.append(":" + d.expr.accept(printExprs) + " ,");

                }
                print.deleteCharAt(print.length() - 1);
                print.append("]{ \r\n");
                print.append(f.getBody().accept(printExprs) + " \r\n}\r\n");

            }
        }
    }

    private void printFacts(Module newModule, StringBuilder print, printExpr printExprs) {
        for (Pair<String,Expr> f : newModule.getAllFacts()) {

            print.append("\r\nfact ");
            if (f.a.startsWith("fact$")) {
                print.append(" {");

            } else {
                print.append("  " + f.a + " {");
            }
            print.append(f.b.accept(printExprs) + "}\r\n");
        }
    }

    private void printSigs(StringBuilder print, ConstList<Sig> sigsFinal, printExpr printExprs) {
        for (int i = 0; i < sigsFinal.size(); i++) {

            Sig s = sigsFinal.get(i);
            if (s.isAbstract != null) {
                print.append("abstract ");
            }

            if (s.isLone != null) {
                print.append("lone ");
            }
            if (s.isOne != null) {
                print.append("one ");
            }
            if (s.isSome != null) {
                print.append("some ");
            }

            print.append("sig " + s.label.substring(5));


            if (s.isSubsig != null) {
                if (((PrimSig) s).parent != UNIV) {
                    print.append(" extends ");
                    // String temp=((Sig.PrimSig) s).parent.label.substring(5);
                    print.append(((PrimSig) s).parent.label.substring(5));
                }
            }

            if (s.isSubset != null) {
                print.append(" in ");
                print.append(((SubsetSig) s).parents.get(0).label.substring(5));

                if (((SubsetSig) s).parents.size() > 1) {
                    for (int j = 1; j < ((SubsetSig) s).parents.size() - 1; j++) {
                        print.append(" + " + ((SubsetSig) s).parents.get(j).label.substring(5));
                    }
                }
            }
            //print fields
            print.append(" { ");
            if (s.getFields().size() > 0) {
                for (Field f : s.getFields()) {
                    print.append("\r\n   " + f.label + " : ");
                    print.append(f.decl().expr.accept(printExprs) + ",");
                }
            }
            print.deleteCharAt(print.length() - 1);
            print.append("}\r\n");
        }
    }



    /**
     * Chnage the type of Fields
     *
     * since the sigs are change so the type of Field(field to sig point) need to be
     * changed
     *
     * @param
     */

    class printExpr extends VisitReturn<String> {


        @Override
        public String visit(ExprBinary x) throws Err {
            if (x.right instanceof ExprBinary) {
                return " " + visitThis(x.left) + " " + x.op.toString() + " " + visitThis(x.right) + " ";
            }

            return " " + visitThis(x.left) + " " + x.op.toString() + " " + visitThis(x.right) + " ";

        }

        @Override
        public String visit(ExprList x) throws Err {
            StringBuilder strtemp = new StringBuilder();
            String name = null;
            if (x.op.equals(ExprList.Op.AND)) {
                name = " and ";
            } else if (x.op.equals(ExprList.Op.OR)) {
                name = " or ";

            } else if (x.op.equals(ExprList.Op.DISJOINT)) {
                name = "disjoint";

            } else if (x.op.equals(ExprList.Op.TOTALORDER)) {
                name = "totalorder";

            }
            if (x.op.equals(ExprList.Op.AND) || x.op.equals(ExprList.Op.OR)) {
                if (x.args.size() > 0) {
                    strtemp.append(visitThis(x.args.get(0)));
                    if (x.args.size() > 1) {
                        for (int i = 1; i < x.args.size(); i++) {
                            strtemp.append(name + " \r\n    " + visitThis(x.args.get(i)));
                        }
                    }
                }
            }
            return strtemp.toString();
        }

        @Override
        public String visit(ExprCall x) throws Err {
            StringBuilder temp = new StringBuilder();
            temp.append(x.fun.label.substring(x.fun.label.indexOf("/") + 1));
            if (x.args.size() > 0) {
                temp.append("[");
                for (Expr arg : x.args) {
                    temp.append(visitThis(arg) + ",");
                }
                temp.deleteCharAt(temp.length() - 1);
                temp.append("]");
            }
            return temp.toString();

        }

        @Override
        public String visit(ExprConstant x) throws Err {
            switch (x.op) {
                case TRUE :
                    return " true";
                case FALSE :
                    return " false>";
                case IDEN :
                    return " iden";
                case MAX :
                    return " fun/max";
                case MIN :
                    return " fun/min";
                case NEXT :
                    return " fun/next";
                case EMPTYNESS :
                    return " none";
                case STRING :
                    return " " + x.string;
            }
            return " " + x.num;
        }

        @Override
        public String visit(ExprITE x) throws Err {
            return null;
        }

        @Override
        public String visit(ExprLet x) throws Err {
            return null;
        }

        @Override
        public String visit(ExprQt x) throws Err {
            StringBuilder s = new StringBuilder();
            if (!x.op.equals(ExprQt.Op.COMPREHENSION)) {
                s.append(x.op.toString() + " ");
            } else {
                s.append("{");
            }

            for (Decl decl : x.decls) {
                for (Expr e : decl.names) {
                    s.append(visitThis(e) + " ,");
                }
                s.deleteCharAt(s.length() - 1);
                s.append(": ");
                s.append(visitThis(decl.expr) + ",");
            }
            s.deleteCharAt(s.length() - 1);
            if (x.op.equals(ExprQt.Op.COMPREHENSION)) {
                s.append("}");
            }

            s.append("|");

            //表达式
            s.append(visitThis(x.sub));

            return s.toString();

        }

        @Override
        public String visit(ExprUnary x) throws Err {
            switch (x.op) {
                case NOOP :
                case CAST2INT :
                case CAST2SIGINT :
                    return visitThis(x.sub);
                default :
                    return x.op.toString().replaceAll(" of", " ") + " " + visitThis(x.sub);
            }

        }

        @Override
        public String visit(ExprVar x) throws Err {
            return x.label;
        }

        @Override
        public String visit(Sig x) throws Err {
            if (x.builtin) {
                return x.label;
            } else
                return x.label.substring(5);
        }

        @Override
        public String visit(Field x) throws Err {
            return x.label;
        }
    }

    /*
     * private void changeTypepOfField(ConstList.TempList<Sig> finalSig) { for(int
     * i=0;i<finalSig.size();i++){ for (Sig.Field f: finalSig.get(i).getFields()){
     * Type t=f.type; ConstList.TempList<Type.ProductType> entries =new
     * ConstList.TempList<>(); // ConstList<ProductType> for(Type.ProductType
     * productTypes :t.getEntities()){ Sig.PrimSig newPrimsigs[]=new
     * Sig.PrimSig[productTypes.getTypes().length]; // PrimSig[] types; for (int
     * j=0; j< productTypes.getTypes().length;j++){
     * if(sigOld2new.containsKey(productTypes.get(j))&&
     * sigOld2new.get(productTypes.get(j))!=null){ newPrimsigs[j]=(Sig.PrimSig)
     * sigOld2new.get(productTypes.get(j)); } else
     * newPrimsigs[j]=productTypes.get(j); } Type.ProductType p=new
     * Type.ProductType(newPrimsigs); entries.add(p); } Type newType=new
     * Type(t.is_bool,entries.makeConst(),t.arity()); f.type=newType; } } } /* /**
     * construct sigs in the new AST tree
     */
    class reconstructSigs extends VisitReturn<Expr> {

        @Override
        public Expr visit(ExprBinary x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            return null;

        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            return null;
        }

        @Override
        public Expr visit(Sig x) throws Err {

            Sig signew = null;
            // not marked with Negtive features,
            if (!containsNegaF(x)) {

                // not marked or subset of selected features
                if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {

                    //used to generate new Sig
                    Attr[] attributes = new Attr[x.attributes.size()];
                    for (int i = 0; i < x.attributes.size(); i++) {
                        attributes[i] = x.attributes.get(i);
                    }


                    if (x instanceof PrimSig) {
                        signew = new PrimSig(x.label, ((PrimSig) x).parent, attributes);
                    } else if (x instanceof SubsetSig) {
                        signew = new SubsetSig(x.label, ((SubsetSig) x).parents, attributes);
                    }

                    signew.attributes = x.attributes;

                    ConstList.TempList<Field> tempList = new ConstList.TempList<>();
                    if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                        for (Field f : x.getFields()) {
                            f.sig = signew;

                            Expr exprout = visitThis(f);
                            if (exprout != null) {

                                //修改指针
                                //   changePoint(exprout,x,xnew);

                                //help to find the old Field
                                List<Field> listold = signew.getFields().makeCopy();

                                signew.addField(f.label, exprout);
                                List<Field> list = signew.getFields().makeCopy();

                                list.removeAll(listold);
                                // field2newField.put(f,list.get(0));
                            }
                        }
                    }
                }
            }
            if (sigOld2new.containsKey(x)) {
                sigOld2new.put(x, signew);
            }

            return signew;
        }

        @Override
        public Expr visit(Field x) throws Err {

            if (!containsNegaF(x)) {
                if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                    Expr fnew = x.decl().expr;
                    //the type of field point to old Sigs
                    return fnew;
                }
            }
            return null;
        }
    }



    /**
     * used to project Expr
     */
    //  [] colorful Alloy
    // just project the Expr, does not change the "type" of Expr and point to old sigs
    class reconstructAST extends VisitReturn<Expr> {

        @Override
        public Expr visit(ExprBinary x) throws Err {
            Expr leftExpr = null;
            Expr rightExpr = null;
            //not marked with neg feature
            if (!containsNegaF(x)) {
                //Expr not marked or marked is subSet of selected (select F1,f2, marked F1)
                if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                    leftExpr = visitThis(x.left);
                    rightExpr = visitThis(x.right);
                }
            }
            if (leftExpr == null)
                return rightExpr;
            else if (rightExpr == null) {
                return leftExpr;
            } else
                return x.op.make(x.pos, x.closingBracket, leftExpr, rightExpr);
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            ConstList.TempList<Expr> temp = new ConstList.TempList<>(x.args.size());
            if (!containsNegaF(x)) {
                if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                    for (Expr expr : x.args) {
                        if (visitThis(expr) != null) {
                            temp.add(visitThis(expr));
                        }
                    }
                }
                return ExprList.make(x.pos, x.closingBracket, x.op, temp.makeConst());
            }
            return null;
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            if (!containsNegaF(x)) {
                if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                    return x;
                }
            }
            return null;
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            if (x.color.isEmpty()) {
                return x;
            }
            //not marked with neg Feature
            else if (!containsNegaF(x)) {
                //select F1,f2, marked F1
                if (selectedFeature.containsAll(x.color)) {
                    return x;
                }
            }
            return null;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            Expr cond = null;
            Expr leftExpr = null;
            Expr rightExpr = null;
            if (!containsNegaF(x)) {
                //select F1,f2, marked F1
                if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                    cond = visitThis(x.cond);
                    leftExpr = visitThis(x.left);
                    rightExpr = visitThis(x.right);
                }
                return ExprITE.make(x.pos, cond, leftExpr, rightExpr);
            }

            return null;
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            /*
             * //change the type of expr,used in Execute Type t=x.type;
             * ConstList.TempList<Type.ProductType> entries =new ConstList.TempList<>();
             * //ConstList<ProductType> entries // PrimSig[] types; //for each ProductType
             * Iterator<Type.ProductType> iterator= t.iterator(); while(
             * iterator.hasNext()){ Sig.PrimSig newPrimsigs[]=new
             * Sig.PrimSig[iterator.next().arity()]; for (int j=0;
             * j<iterator.next().arity();j++){ if(sigOld2new.containsKey(iterator.next())&&
             * sigOld2new.get(iterator.next())!=null){ newPrimsigs[j]=(Sig.PrimSig)
             * sigOld2new.get(iterator.next()); } else newPrimsigs[j]=productTypes.get(j); }
             * } Type newType=new Type(t.is_bool,entries.makeConst(),t.arities);
             * x.type=newType;
             */
            if (!containsNegaF(x)) {
                if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                    return x;
                }
            }
            return null;
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            //project decls-------------
            ConstList.TempList<Decl> decls = new ConstList.TempList<Decl>(x.decls.size());
            for (Decl d : x.decls) {
                ConstList.TempList<ExprVar> declsnames = new ConstList.TempList<ExprVar>(x.decls.size());
                Expr exp = visitThis(d.expr);

                if (exp != null) {
                    for (ExprHasName v : d.names) {
                        Expr Exprout = visitThis(v);
                        declsnames.add((ExprVar) Exprout);
                    }


                    if (declsnames.size() != 0) {

                        Decl dd = new Decl(d.isPrivate, d.disjoint, d.disjoint2, declsnames.makeConst(), exp);
                        decls.add(dd);
                    }
                }
            }
            //project body
            Expr sub = visitThis(x.sub);


            if (sub != null && decls.size() != 0) {
                return x.op.make(x.pos, x.closingBracket, decls.makeConst(), sub);
            }

            return null;
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            Expr tempExpr = null;
            if (!containsNegaF(x)) {
                if (x.op.equals(ExprUnary.Op.NOOP) && (x.sub instanceof Field || x.sub instanceof Sig)) {
                    if (x.color.isEmpty() || selectedFeature.containsAll(x.color)) {
                        return x;
                    }

                } else if (selectedFeature.containsAll(x.color)) {
                    tempExpr = visitThis(x.sub);
                    if (tempExpr != null) {
                        tempExpr = x.op.make(x.pos, tempExpr);
                    }

                }

            }
            return tempExpr;

        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            /*
             * //change Expr type Type t=x.type; ConstList.TempList<Type.ProductType>
             * entries =new ConstList.TempList<>(); //ConstList<ProductType> entries //
             * PrimSig[] types; //每一个 ProductType for(Type.ProductType productTypes
             * :t.getEntities()){ Sig.PrimSig newPrimsigs[]=new
             * Sig.PrimSig[productTypes.getTypes().length]; for (int j=0; j<
             * productTypes.getTypes().length;j++){
             * if(sigOld2new.containsKey(productTypes.get(j))&&
             * sigOld2new.get(productTypes.get(j))!=null){ newPrimsigs[j]=(Sig.PrimSig)
             * sigOld2new.get(productTypes.get(j)); } else
             * newPrimsigs[j]=productTypes.get(j); } Type.ProductType p=new
             * Type.ProductType(newPrimsigs); entries.add(p); } Type newType=new
             * Type(t.is_bool,entries.makeConst(),t.arities); x.type=newType;
             */
            // golable feature
            if (x.color.isEmpty()) {
                return x;
            }
            //not marked with negative
            else if (!containsNegaF(x)) {
                //select F1,f2, marked F1
                if (isSetEqual(selectedFeature, x.color)) {
                    return x;
                }
            }
            return null;
        }

        @Override
        public Expr visit(Sig x) throws Err {

            if (x.color.isEmpty())
                return x;

            if (!containsNegaF(x) && selectedFeature.containsAll(x.color))
                return x;
            return null;
        }

        @Override
        public Expr visit(Field x) throws Err {
            if (x.color.isEmpty())
                return x;
            if (!containsNegaF(x) && selectedFeature.containsAll(x.color))
                return x;

            return null;
        }
    }


    //generate Union Module
    class printUnionModule extends VisitReturn<String> {

        @Override
        public String visit(ExprBinary x) throws Err {
            //only for + ,&  operator

            Set<Integer> NFeatures = new HashSet<>();
            Set<Integer> PFeatures = new HashSet<>();
            for (Integer i : x.color) {
                if (i < 0)
                    NFeatures.add(-i);
                else
                    PFeatures.add(i);
            }

            StringBuilder str = new StringBuilder();

            int arity = x.type.arity();
            int arityLeft = x.left.type.arity();
            if (!x.color.isEmpty()) {
                if (!NFeatures.isEmpty()) {

                    addFeatureprefix(PFeatures, str, "not in", "and");
                    str.append(visitThis(x.left));
                    str.append(x.op.toString());
                    str.append(visitThis(x.right));
                }


                if (!PFeatures.isEmpty()) { //Fi in Product implies

                    addFeatureprefix(PFeatures, str, "in", "and");
                    str.append(visitThis(x.left));
                    str.append(x.op.toString());
                    str.append(visitThis(x.right));
                }

            }

            //check left

            // ---print x.left --------------------------------------------------------
            //x.left marked
            if (!x.left.color.isEmpty()) {
                // "F in product implies"

                Set<Integer> NFeaturesleft = new HashSet<>();
                Set<Integer> PFeaturesleft = new HashSet<>();
                for (Integer i : x.left.color) {
                    if (i < 0)
                        NFeaturesleft.add(-i);
                    else
                        PFeaturesleft.add(i);
                }
                str.append("(");
                str.append(visitThis(x.left));
                str.append(" else ");
                // and : " none-> none-> none->......" (&:   "univ->univ->univ..." )
                printElse(str, arityLeft, x);
                str.append(")");
            } else
                str.append(visitThis(x.left));


            // ---print x.op  ---------
            str.append(x.op.toString());
            //-----print x.right ------
            str.append(visitThis(x.right));

            return str.toString();
        }

        @Override
        public String visit(ExprList x) throws Err {

            StringBuilder str = new StringBuilder();

            Set<Integer> NFeatures = new HashSet<>();
            Set<Integer> PFeatures = new HashSet<>();
            for (Integer i : x.color) {
                if (i < 0)
                    NFeatures.add(-i);
                else
                    PFeatures.add(i);
            }
            //x marked
            if (!x.color.isEmpty()) {
                //Marked with NFeature
                if (!NFeatures.isEmpty()) {
                    str.append("(");
                    addFeatureprefix(PFeatures, str, "not in", "and");

                    for (Expr arg : x.args) {
                        str.append(" " + visitThis(arg));
                        str.append(" " + x.op.name());
                    }

                }

                if (!PFeatures.isEmpty()) {
                    //F in Product implies
                    str.append("(");
                    addFeatureprefix(PFeatures, str, "in", "and");

                    for (Expr arg : x.args) {
                        str.append(" " + visitThis(arg));
                        str.append(" " + x.op.name());
                    }
                }

                str.deleteCharAt(str.length() - 1);
                str.deleteCharAt(str.length() - 1);
                if (x.op.equals(ExprList.Op.AND))
                    str.deleteCharAt(str.length() - 1);
                str.append(")");
            }


            //--------------------x.argi (i=0,1,2,3)----------------
            for (Expr arg : x.args) {
                str.append("\r\n    ");
                if (arg.color.isEmpty()) {
                    str.append(visitThis(arg));
                } else {
                    // x not marked but arg i marked
                    Set<Integer> NFeaturessub = new HashSet<>();
                    Set<Integer> PFeaturessub = new HashSet<>();
                    for (Integer i : x.color) {
                        if (i < 0)
                            NFeaturessub.add(-i);
                        else
                            PFeaturessub.add(i);
                    }
                    str.append("(");
                    str.append(visitThis(arg));
                    // str.append(" else ");
                    //printElse(str,x);
                    str.append(")");
                }
                String name = x.op.name();
                if (name.equals("AND"))
                    name = "and";
                if (name.equals("OR"))
                    name = "or";
                str.append(name);
            }

            // delete the last "or" or "and" string
            str.deleteCharAt(str.length() - 1);
            str.deleteCharAt(str.length() - 1);

            if (x.op.equals(ExprList.Op.AND))
                str.deleteCharAt(str.length() - 1);
            return str.toString();
        }

        @Override
        public String visit(ExprCall x) throws Err {

            StringBuilder str = new StringBuilder();

            StringBuilder tempExpr = new StringBuilder();
            tempExpr.append(x.fun.label.substring(x.fun.label.indexOf("/") + 1));
            if (x.args.size() > 0)
                tempExpr.append("[");
            for (Expr arg : x.args) {
                tempExpr.append(visitThis(arg) + ",");
            }
            tempExpr.deleteCharAt(tempExpr.length() - 1);

            if (x.args.size() > 0)
                tempExpr.append("]");


            Set<Integer> NFeatures = new HashSet<>();
            Set<Integer> PFeatures = new HashSet<>();
            for (Integer i : x.color) {
                if (i < 0)
                    NFeatures.add(-i);
                else
                    PFeatures.add(i);
            }


            if (!x.color.isEmpty()) {

                if (!NFeatures.isEmpty()) {
                    addFeatureprefix(PFeatures, str, "not in", "and");
                    str.append(tempExpr);

                }
                if (!PFeatures.isEmpty()) {
                    addFeatureprefix(NFeatures, str, "in", "and");
                    str.append(tempExpr);
                }
            } else {

                str.append(tempExpr);
            }
            return str.toString();

        }

        @Override
        public String visit(ExprConstant x) throws Err {
            StringBuilder str = new StringBuilder();
            StringBuilder tempExpr = new StringBuilder();


            if (x.op.equals(ExprConstant.Op.TRUE))
                tempExpr.append(" true ");
            if (x.op.equals(ExprConstant.Op.FALSE))
                tempExpr.append(" false ");
            if (x.op.equals(ExprConstant.Op.IDEN))
                tempExpr.append(" iden ");

            if (x.op.equals(ExprConstant.Op.MAX))
                tempExpr.append(" fun/max ");
            if (x.op.equals(ExprConstant.Op.MIN))
                tempExpr.append(" fun/min ");
            if (x.op.equals(ExprConstant.Op.NEXT))
                tempExpr.append(" fun/next ");
            if (x.op.equals(ExprConstant.Op.EMPTYNESS))
                tempExpr.append(" none ");
            if (x.op.equals(ExprConstant.Op.STRING))
                tempExpr.append(" " + x.string + " ");
            if (x.op.equals(ExprConstant.Op.NUMBER))
                tempExpr.append(" " + x.num + " ");


            if (!x.color.isEmpty()) {
                Set<Integer> NFeatures = new HashSet<>();
                Set<Integer> PFeatures = new HashSet<>();
                for (Integer i : x.color) {
                    if (i < 0)
                        NFeatures.add(-i);
                    else
                        PFeatures.add(i);
                }


                if (!NFeatures.isEmpty()) {
                    addFeatureprefix(PFeatures, str, "not in", "and");
                    str.append(tempExpr);

                }
                if (!PFeatures.isEmpty()) {
                    addFeatureprefix(NFeatures, str, "in", "and");
                    str.append(tempExpr);
                }


            } else
                str.append(tempExpr);

            return str.toString();
        }

        @Override
        public String visit(ExprITE x) throws Err {
            StringBuilder str = new StringBuilder();



            if (!x.color.isEmpty()) {
                Set<Integer> NFeatures = new HashSet<>();
                Set<Integer> PFeatures = new HashSet<>();
                for (Integer i : x.color) {
                    if (i < 0)
                        NFeatures.add(-i);
                    else
                        PFeatures.add(i);
                }


                if (!NFeatures.isEmpty()) {
                    addFeatureprefix(PFeatures, str, "not in", "and");

                    str.append(visitThis(x.cond));
                    str.append(" implies ");

                    str.append(visitThis(x.left));
                    str.append(" else ");
                    str.append(visitThis(x.right));


                }
                if (!PFeatures.isEmpty()) {
                    addFeatureprefix(NFeatures, str, "in", "and");
                    str.append(visitThis(x.cond));
                    str.append(" implies ");

                    str.append(visitThis(x.left));
                    str.append(" else ");
                    str.append(visitThis(x.right));
                }


            } else {
                str.append(visitThis(x.cond));
                str.append(" implies ");

                str.append(visitThis(x.left));
                str.append(" else ");
                str.append(visitThis(x.right));
            }



            return str.toString();
        }

        @Override
        public String visit(ExprLet x) throws Err {
            StringBuilder str = new StringBuilder();
            str.append(visitThis(x.var));
            str.append("=");

            str.append(visitThis(x.expr));
            return str.toString();

        }

        @Override
        public String visit(ExprQt x) throws Err {
            StringBuilder str = new StringBuilder();

            StringBuilder tempExpr = new StringBuilder();

            if (!x.op.equals(ExprQt.Op.COMPREHENSION))
                //all
                tempExpr.append(x.op.toString() + " ");

            for (Decl decl : x.decls) {
                for (Expr e : decl.names) {
                    tempExpr.append(visitThis(e) + " ,");
                }
                tempExpr.deleteCharAt(str.length() - 1);
                tempExpr.append(": ");
                tempExpr.append(visitThis(decl.expr) + ",");
            }
            tempExpr.deleteCharAt(str.length() - 1);

            tempExpr.append("|");

            tempExpr.append(visitThis(x.sub));



            if (!x.color.isEmpty()) {
                Set<Integer> NFeatures = new HashSet<>();
                Set<Integer> PFeatures = new HashSet<>();
                for (Integer i : x.color) {
                    if (i < 0)
                        NFeatures.add(-i);
                    else
                        PFeatures.add(i);
                }

                if (!NFeatures.isEmpty()) {
                    addFeatureprefix(NFeatures, str, "not in", "and");
                    str.append(tempExpr);
                }
                if (!PFeatures.isEmpty()) {
                    addFeatureprefix(PFeatures, str, "in", "and");
                    str.append(tempExpr);
                }



            } else
                str.append(tempExpr);

            return str.toString();
        }

        @Override
        public String visit(ExprUnary x) throws Err {
            Set<Integer> NFeatures = new HashSet<>();
            Set<Integer> PFeatures = new HashSet<>();
            for (Integer i : x.color) {
                if (i < 0)
                    NFeatures.add(-i);
                else
                    PFeatures.add(i);
            }

            StringBuilder str = new StringBuilder();

            StringBuilder tempExpr = new StringBuilder();
            if (x.op.equals(ExprUnary.Op.SETOF))
                tempExpr.append(" set ");
            if (x.op.equals(ExprUnary.Op.SOMEOF))
                tempExpr.append(" some ");
            if (x.op.equals(ExprUnary.Op.LONEOF))
                tempExpr.append(" lone ");
            if (x.op.equals(ExprUnary.Op.ONEOF))
                tempExpr.append(" ");
            if (x.op.equals(ExprUnary.Op.EXACTLYOF))
                tempExpr.append(" exactly ");
            if (x.op.equals(ExprUnary.Op.NOT) || x.op.equals(ExprUnary.Op.NO) || x.op.equals(ExprUnary.Op.SOME) || x.op.equals(ExprUnary.Op.ONE) || x.op.equals(ExprUnary.Op.LONE) || x.op.equals(ExprUnary.Op.TRANSPOSE) || x.op.equals(ExprUnary.Op.RCLOSURE) || x.op.equals(ExprUnary.Op.CLOSURE) || x.op.equals(ExprUnary.Op.CARDINALITY))
                tempExpr.append(" " + x.op.toString() + " ");
            tempExpr.append(visitThis(x.sub));


            if (!x.color.isEmpty()) {
                //negative Feature
                if (!NFeatures.isEmpty())
                    addFeatureprefix(NFeatures, str, "not in", "and");

                if (!PFeatures.isEmpty())
                    addFeatureprefix(PFeatures, str, "in", "and");
            }

            str.append(tempExpr);
            return str.toString();
        }

        @Override
        public String visit(ExprVar x) throws Err {

            // StringBuilder str=new StringBuilder();
            // if(!x.color.isEmpty())
            // addFeatureprefix(str, x);
            // str.append(x.label);

            return " " + x.label + " ";

        }

        @Override
        public String visit(Sig x) throws Err {
            return x.label.substring(5) + " ";
        }

        @Override
        public String visit(Sig.Field x) throws Err {
            return x.label + " ";
        }

    }

    /**
     * for ExprList "and","or" operator
     *
     * @param str
     * @param x
     *
     */

    private void printElse(StringBuilder str, int arity, ExprBinary x) {

        //    + operator
        if (x.op.equals(ExprBinary.Op.PLUS))
            printElseString(str, arity, " none ");
        //   & operator
        if (x.op.equals(ExprBinary.Op.INTERSECT))
            printElseString(str, arity, " univ ");
    }



    private void printElseString(StringBuilder str, int arity, String s) {
        StringBuilder elseString = new StringBuilder();
        for (int i = 0; i < arity; i++) {
            elseString.append(" none " + "->");
        }
        elseString.deleteCharAt(elseString.length() - 1);
        elseString.deleteCharAt(elseString.length() - 1);
        str.append(elseString);
    }

    /**
     *
     *
     * @param str
     * @param
     * @param
     * @param
     */

    private void addFeatureprefix(Set<Integer> PFeature, StringBuilder str, String inOrNot, String operator) {

        if (PFeature.size() > 1)
            str.append("    (");

        for (Integer i : PFeature) {

            str.append(" F" + i + " " + inOrNot + " Product " + operator);
        }
        if (str.length() >= 2) {

            str.deleteCharAt(str.length() - 1);
            str.deleteCharAt(str.length() - 1);
            if (operator.equals("and"))
                str.deleteCharAt(str.length() - 1);

        }

        if (PFeature.size() > 1)
            str.append(")");
        str.append(" implies ");
    }

    /**
     *
     * @param expr The expression to be projected
     * @return true if expr is marked with Negative Feature (expr marked -1,
     *         selected 1)
     */
    // colorful Alloy
    private boolean containsNegaF(Expr expr) {
        for (Integer i : selectedFeature) {
            if (expr.color.contains(-i)) {
                return true;
            }
        }
        return false;
    }


    /**
     * compute if the two set "set1" and "set2" are equal
     *
     * @param set1
     * @param set2
     * @return
     */
    private Boolean isSetEqual(Set set1, Set set2) {
        if (set1 == null && set2 == null) {
            return true; // Both are null
        }

        if (set1 == null || set2 == null || set1.size() != set2.size() || set1.size() == 0 || set2.size() == 0) {
            return false;
        }
        //  Iterator ite1 = set1.iterator();
        Iterator ite2 = set2.iterator();

        boolean isFullEqual = true;

        while (ite2.hasNext()) {
            if (!set1.contains(ite2.next())) {
                isFullEqual = false;
            }
        }
        return isFullEqual;
    }

}
