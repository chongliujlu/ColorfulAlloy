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

package edu.mit.csail.sdg.alloy4;

import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.util.*;
import java.util.List;

import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.AbstractDocument;
import javax.swing.text.BadLocationException;
import javax.swing.text.BoxView;
import javax.swing.text.Document;
import javax.swing.text.Element;
import javax.swing.text.LabelView;
import javax.swing.text.StyledEditorKit;
import javax.swing.text.View;
import javax.swing.text.ViewFactory;

import edu.mit.csail.sdg.alloy4.Listener.Event;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

import static java.awt.event.MouseEvent.BUTTON3;

/**
 * Graphical syntax-highlighting editor.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread
 */

public final class OurSyntaxWidget {

    /**
     * The current list of listeners; possible events are { STATUS_CHANGE, FOCUSED,
     * CTRL_PAGE_UP, CTRL_PAGE_DOWN, CARET_MOVED }.
     */
    public final Listeners                  listeners        = new Listeners();

    /** The JScrollPane containing everything. */
    private final JScrollPane               component        = OurUtil.make(new JScrollPane(), new EmptyBorder(0, 0, 0, 0));

    /** This is an optional JComponent annotation. */
    public final JComponent                 obj1;

    /** This is an optional JComponent annotation. */
    public final JComponent                 obj2;

    /**
     * The underlying StyledDocument being displayed (changes will trigger the
     * STATUS_CHANGE event)
     */
    private final OurSyntaxUndoableDocument doc              = new OurSyntaxUndoableDocument("Monospaced", 14);

    /** The underlying JTextPane being displayed. */
    private final JTextPane                 pane             = OurAntiAlias.pane(this::getTooltip, Color.BLACK, Color.WHITE, new EmptyBorder(6, 6, 6, 6));

    //colorful merge
    /**
     * The right-click context menu associated with this JPanel.
     */
    public final JPopupMenu   pop              = new JPopupMenu();
    /**
     * The filename for this JTextPane (changes will trigger the STATUS_CHANGE
     * event)
     */
    private String                          filename         = "";

    /**
     * the file modification date for the file loaded. If no file is loaded
     * (!isFile), this must be -1.
     */
    private long                            fileModifiedDate = -1;

    /**
     * Whether this JTextPane has been modified since last load/save (changes will
     * trigger the STATUS_CHANGE event)
     */
    private boolean                         modified;

    /**
     * Whether this JTextPane corresponds to an existing disk file (changes will
     * trigger the STATUS_CHANGE event)
     */
    private boolean                         isFile;

    /** Caches the most recent background painter if nonnull. */
    private OurHighlighter                  painter;

    private OurTabbedSyntaxWidget           parent;

    private volatile CompModule             module;

    /**
     * Constructs a syntax-highlighting widget.
     */
    public OurSyntaxWidget(OurTabbedSyntaxWidget parent) {
        this(parent, true, "", "Monospaced", 14, 4, null, null);
    }

    /**
     * Constructs a syntax-highlighting widget.
     *
     * @param parent
     */
    @SuppressWarnings("serial" )
    public OurSyntaxWidget(OurTabbedSyntaxWidget parent, boolean enableSyntax, String text, String fontName, int fontSize, int tabSize, JComponent obj1, JComponent obj2) {
        pane.addKeyListener(new KeyListener() {

            @Override
            public void keyTyped(KeyEvent e) {
                module = null;
            }

            @Override
            public void keyReleased(KeyEvent e) {
                module = null;
            }

            @Override
            public void keyPressed(KeyEvent e) {
                module = null;
            }
        });
        this.parent = parent;
        this.obj1 = obj1;
        this.obj2 = obj2;
        final OurSyntaxWidget me = this;
        final ViewFactory defaultFactory = (new StyledEditorKit()).getViewFactory();
        doc.do_enableSyntax(enableSyntax);
        doc.do_setFont(fontName, fontSize, tabSize);
        pane.setEditorKit(new StyledEditorKit() { // Prevents line-wrapping up to width=30000, and tells it to use our Document obj

            @Override
            public Document createDefaultDocument() {
                return doc;
            }

            @Override
            public ViewFactory getViewFactory() {
                return new ViewFactory() {

                    public View create(Element x) {
                        if (AbstractDocument.ContentElementName.equals(x.getName()))
                            return new StrekableLabellView(x); // [HASLab] colorful Alloy, strike out
                        if (!AbstractDocument.SectionElementName.equals(x.getName()))
                            return defaultFactory.create(x);
                        return new BoxView(x, View.Y_AXIS) { // 30000 is a good width to use here; value > 32767 appears to cause errors

                            @Override
                            public final float getMinimumSpan(int axis) {
                                return super.getPreferredSpan(axis);
                            }

                            @Override
                            public final void layout(int w, int h) {
                                try {
                                    super.layout(30000, h);
                                } catch (Throwable ex) {}
                            }
                        };
                    }
                };
            }
        });
        if (text.length() > 0) {
            pane.setText(text);
            pane.setCaretPosition(0);
        }
        doc.do_clearUndo();
        // [HASLab] colorful Alloy, add the color features actions
        for (int i = 0; i < 9; i++) {
            final int k = i;
            pane.getActionMap().put("alloy_c" + (i + 1), new AbstractAction("alloy_c" + (i + 1)) {

                public void actionPerformed(ActionEvent e) {
                    try {
                        pane.getDocument().insertString(pane.getSelectionStart(), "" + ((char) (OurSyntaxDocument.O1 + k)), null);
                        if (pane.getSelectionStart() != pane.getSelectionEnd())
                            pane.getDocument().insertString(pane.getSelectionEnd(), "" + ((char) (OurSyntaxDocument.O1 + k)), null);
                        pane.setSelectionEnd(pane.getSelectionEnd() - 1);
                    } catch (BadLocationException e1) {
                        // TODO Auto-generated catch block
                        e1.printStackTrace();
                    }
                }
            });
            pane.getActionMap().put("alloy_s" + (i + 1), new AbstractAction("alloy_s" + (i + 1)) {

                public void actionPerformed(ActionEvent e) {
                    try {
                        pane.getDocument().insertString(pane.getSelectionStart(), "" + ((char) (OurSyntaxDocument.E1 + k)), null);
                        if (pane.getSelectionStart() != pane.getSelectionEnd())
                            pane.getDocument().insertString(pane.getSelectionEnd(), "" + ((char) (OurSyntaxDocument.E1 + k)), null);
                        pane.setSelectionEnd(pane.getSelectionEnd() - 1);
                    } catch (BadLocationException e1) {
                        // TODO Auto-generated catch block
                        e1.printStackTrace();
                    }
                }
            });
        }
        pane.getActionMap().put("alloy_c0", new AbstractAction("alloy_c0") {

            public void actionPerformed(ActionEvent e) {
                try {
                    pane.getDocument().insertString(pane.getSelectionStart(), "" + ("\uD83C\uDD0B"), null);
                    if (pane.getSelectionStart() != pane.getSelectionEnd())
                        pane.getDocument().insertString(pane.getSelectionEnd(), "" + ("\uD83C\uDD0B"), null);
                    pane.setSelectionEnd(pane.getSelectionEnd() - 1);
                } catch (BadLocationException e1) {
                    // TODO Auto-generated catch block
                    e1.printStackTrace();
                }
            }
        });

        pane.getActionMap().put("alloy_copy", new AbstractAction("alloy_copy") {

            @Override
            public void actionPerformed(ActionEvent e) {
                pane.copy();
            }
        });
        pane.getActionMap().put("alloy_cut", new AbstractAction("alloy_cut") {

            @Override
            public void actionPerformed(ActionEvent e) {
                pane.cut();
            }
        });
        pane.getActionMap().put("alloy_paste", new AbstractAction("alloy_paste") {

            @Override
            public void actionPerformed(ActionEvent e) {
                pane.paste();
            }
        });
        pane.getActionMap().put("alloy_ctrl_pageup", new AbstractAction("alloy_ctrl_pageup") {

            @Override
            public void actionPerformed(ActionEvent e) {
                listeners.fire(me, Event.CTRL_PAGE_UP);
            }
        });
        pane.getActionMap().put("alloy_ctrl_pagedown", new AbstractAction("alloy_ctrl_pagedown") {

            @Override
            public void actionPerformed(ActionEvent e) {
                listeners.fire(me, Event.CTRL_PAGE_DOWN);
            }
        });
        pane.getActionMap().put("alloy_tab_insert", new AbstractAction("alloy_tab_insert") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doTabInsert();
            }

        });
        pane.getActionMap().put("alloy_tab_remove", new AbstractAction("alloy_tab_remove") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doTabRemove();
            }

        });

        pane.getActionMap().put("alloy-comment-block", new AbstractAction("alloy-comment-block") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doComment();
            }
        });
        pane.getActionMap().put("alloy-nav", new AbstractAction("alloy-comment-block") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doNav();
            }
        });
        pane.getActionMap().put("select-word", getSelectWordAction());

        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_F3, 0), "alloy-nav");
        pane.getInputMap().put(KeyStroke.getKeyStroke('/', OurConsole.menuShortcutKeyMask), "alloy-comment-block");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, 0), "alloy_tab_insert");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, InputEvent.SHIFT_DOWN_MASK), "alloy_tab_remove");
        // [HASLab] colorful Alloy, keyboard shortcuts
        for (int i = 0; i < 9; i++) {
            pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_1 + i, InputEvent.CTRL_MASK), "alloy_c" + (i + 1));
            pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_1 + i, InputEvent.CTRL_MASK | InputEvent.SHIFT_MASK), "alloy_s" + (i + 1));
        }
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_0, InputEvent.CTRL_MASK), "alloy_c0");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_C, InputEvent.CTRL_MASK), "alloy_copy");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_X, InputEvent.CTRL_MASK), "alloy_cut");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_V, InputEvent.CTRL_MASK), "alloy_paste");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, InputEvent.CTRL_MASK), "alloy_copy");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, InputEvent.SHIFT_MASK), "alloy_paste");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_DELETE, InputEvent.SHIFT_MASK), "alloy_cut");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_UP, InputEvent.CTRL_MASK), "alloy_ctrl_pageup");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_DOWN, InputEvent.CTRL_MASK), "alloy_ctrl_pagedown");
        doc.addDocumentListener(new DocumentListener() {

            @Override
            public void insertUpdate(DocumentEvent e) {
                modified = true;
                listeners.fire(me, Event.STATUS_CHANGE);
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                modified = true;
                listeners.fire(me, Event.STATUS_CHANGE);
            }

            @Override
            public void changedUpdate(DocumentEvent e) {}
        });
        pane.addFocusListener(new FocusAdapter() {

            @Override
            public void focusGained(FocusEvent e) {
                listeners.fire(me, Event.FOCUSED);
            }
        });
        pane.addCaretListener(new CaretListener() {

            @Override
            public void caretUpdate(CaretEvent e) {
                listeners.fire(me, Event.CARET_MOVED);
            }
        });

        //colorful merge,right click
        pane.addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
               //  rightClick or ctrl+leftClick
                if(e.getButton()==BUTTON3 || (e.getButton() == MouseEvent.BUTTON1 && e.isControlDown())){
                    int offset = pane.getCaretPosition();
                    CompModule module = null;
                    try {
                        A4Reporter reporter = new A4Reporter();
                        module = CompUtil.parseEverything_fromString(reporter, getText());

                    } catch (Err err) {
                        // TODO Auto-generated catch block
                        err.printStackTrace();
                    }

                   if (module != null){
                       String text = pane.getText();
                       Pos pos = Pos.toPos(text, offset, offset + 1);
                       //position to show the popup button
                       Point point=pane.getCaret().getMagicCaretPosition();

                       //help store the full features of this expression, since Integer parameter will keep.
                       StringBuilder colString=new StringBuilder();

                       //return the annotated sig/fact/assert/Expr/ Func according to the caret
                       Browsable     er=module.findElementPos(module,pos,colString);
                       List <Integer> tempColor = new ArrayList<>();
                       if(colString.length()>0){
                           String [] strs=colString.toString().split(",");
                           for(int i = 0;i<strs.length;i++){
                               tempColor.add(Integer.parseInt(strs[i]));
                           }
                       }
                       //features before merge
                       Set featsBefore=new HashSet(tempColor);

                       if(er !=null){
                           //use a map to store the features that can be removed
                           Map<Set<Integer>,Integer> featRmSet=new HashMap<>();//<feature can be removed, full feature set>
                           Expr facts=module.getAllReachableFacts();
                           if(facts instanceof ExprList)
                               for(Expr f:((ExprList) facts).args){
                                   if(f.toString().equals("some none")){
                                       if(f instanceof ExprUnary && ((ExprUnary) f).op.equals(ExprUnary.Op.NOOP))
                                           f=((ExprUnary) f).sub;
                                       if(f.color.entrySet().size()==2){
                                           for(Integer i: f.color.keySet()){
                                               for(Integer j: f.color.keySet()){
                                                   if(j==i) continue;
                                                   else{
                                                       Set temp=new HashSet<>();
                                                       temp.add(i);
                                                       temp.add(-j);
                                                       featRmSet.put(temp,-j);
                                                   }
                                               }
                                           }
                                       }
                                   }
                               }

                          if (!featRmSet.isEmpty()){
                              if(er instanceof Sig){
                                  for(Sig.Field field: ((Sig) er).getFields()){
                                      Map<Integer,Pos> col=new HashMap(field.color);
                                      for(Map.Entry<Integer,Pos> c:field.color.entrySet()){
                                          if(er.color.containsKey(c.getKey()))
                                              if(er.color.get(c.getKey()).equals(c.getValue()))
                                                  col.remove(c.getKey());
                                      }
                                      for(Map.Entry<Integer, Pos> map:col.entrySet()){
                                          if(field.pos!=null)
                                              field.pos=field.pos.merge(map.getValue());
                                      }
                                      //delete a feature for Field
                                      if(field.pos!=null && field.pos.contains(pos) && !col.isEmpty()){
                                          featsBefore.addAll(field.color.keySet());
                                          er=field;
                                          er.color=col;
                                          break;
                                      }
                                  }
                                  //deleter a feature of a sig/Field
                                  doFeatRmOrAdd(featRmSet,featsBefore,er,point.x, point.y);

                              }else if(er instanceof Expr){
                                  //delete features for facts/assert/Expr
                                  doFeatRmOrAdd(featRmSet,new HashSet<>(featsBefore),er,point.x, point.y);
                              }else if(er instanceof Func){
                                  //delete features for the whole pred/fun
                                  doFeatRmOrAdd(featRmSet,er.color.keySet(),er,point.x, point.y);
                              }else if(er instanceof Command){
                                  doFeatRM(featRmSet, (Command) er,point.x, point.y);
                              }
                          }
                       }
                   }
                }
            }



            //colorful merge
            /**
             * show popUp menu
             * @param featRmSet feats sets that can be removed
             * @param featsBefore feats before remove (include features in parent Expr)
             * @param e expr that can be remove or add features, color only containds Explicit feature annotation in the expr(not parent)
             * @param x x position to show the popup menu
             * @param y y position to show the popup menu
             */
            private void doFeatRmOrAdd(Map<Set<Integer>, Integer> featRmSet, Set<Integer> featsBefore, Browsable e, int x, int y) {
                pop.removeAll();
                Set <Integer> menu=new HashSet<>();
                for(Map.Entry<Set<Integer>, Integer> entry:featRmSet.entrySet()){
                   if(featsBefore.containsAll(entry.getKey()) && e.color.keySet().contains(entry.getValue())){
                       if(!menu.contains(entry.getValue())){
                           menu.add(entry.getValue());
                           JMenuItem item = new JMenuItem("Remove "+getColorString(entry.getValue()));
                           pop.add(item);
                           item.addActionListener(new ActionListener() {
                               @Override
                               public void actionPerformed(ActionEvent event) {
                                   Pos pos=e.color.get(entry.getValue());
                                   int c = getLineStartOffset(pos.y2 - 1) + pos.x2 - 1;
                                   int d= getLineStartOffset(pos.y - 1) + pos.x - 1;
                                   changeText(c,c+1,"");
                                   changeText(d,d+1,"");
                               }
                           });
                       }
                   }
               }
               //Add Features
                //计算removeFeatures
                Map<Set<Integer>, Integer> featAddSet =new HashMap<>(featRmSet);
                for(Map.Entry<Set<Integer>, Integer> entry:featRmSet.entrySet()){
                   Set <Integer> addFeat=new HashSet<>(entry.getKey());
                   addFeat.remove(entry.getValue());
                    featAddSet.put(addFeat,entry.getValue());
                }

                menu=new HashSet<>();
                for(Map.Entry<Set<Integer>, Integer> entry:featAddSet.entrySet()){
                    if(featsBefore.containsAll(entry.getKey()) && !featsBefore.contains(entry.getValue())){
                        if(!menu.contains(entry.getValue())){
                            menu.add(entry.getValue());
                            JMenuItem item = new JMenuItem("Add "+getColorString(entry.getValue()));
                            pop.add(item);
                            item.addActionListener(new ActionListener() {
                                @Override
                                public void actionPerformed(ActionEvent event) {
                                    if(e instanceof Expr){
                                        Pos pos= ((Expr) e).pos;
                                        int c = getLineStartOffset(pos.y2 - 1) + pos.x2 - 1;
                                        int d= getLineStartOffset(pos.y - 1) + pos.x - 1;
                                        changeText(c+1,c+1,getColorString(entry.getValue()));
                                        changeText(d,d,getColorString(entry.getValue()));
                                    }
                                }
                            });
                        }
                    }
                }

                pop.show(pane, x, y);
            }
            private void doFeatRM(Map<Set<Integer>, Integer> featRmSet, Command cmd, int x, int y) {
                pop.removeAll();
                if(cmd.feats!=null){


                Set <Integer> menu=new HashSet<>();
                for(Map.Entry<Set<Integer>, Integer> entry:featRmSet.entrySet()){
                    if(cmd.feats.feats.containsAll(entry.getKey())){
                        if(!menu.contains(entry.getValue())){
                            menu.add(entry.getValue());
                            JMenuItem item = new JMenuItem("Remove "+getColorString(entry.getValue()));
                            pop.add(item);
                            item.addActionListener(new ActionListener() {
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                    Pos pos=cmd.feats.pos;
                                    cmd.feats.feats.remove(entry.getValue());
                                    Pos temp=null;
                                    StringBuilder featsString= new StringBuilder();

                                    if(cmd.feats==null || (cmd.feats.feats.size()==0)){
                                        temp=new Pos(cmd.feats.pos.filename,cmd.feats.pos.x,cmd.feats.pos.y,cmd.pos.x2,cmd.pos.y2);
                                    }else{
                                         featsString= new StringBuilder(getComandColorString(new HashSet<>(cmd.feats.feats)));
                                        temp=new Pos(cmd.feats.pos.filename,cmd.feats.pos.x2,cmd.feats.pos.y2,cmd.pos.x2,cmd.pos.y2);
                                    }


                                    featsString.append(" for ");
                                    featsString.append(cmd.overall > 0 ? cmd.overall + " " : 4 + " ");

                                    if (cmd.scope.size() >= 1 || cmd.bitwidth != -1)
                                        featsString.append(" but ");
                                    if (cmd.bitwidth != -1) {
                                        featsString.append(cmd.bitwidth + " Int ");
                                        if(!cmd.scope.isEmpty() )
                                            featsString.append(",");
                                    }

                                    for (CommandScope cs : cmd.scope) {

                                        if (cs.isExact)
                                            featsString.append(" exactly ");
                                        featsString.append(cs.startingScope + " ");
                                        featsString.append(cs.sig.label.substring(5) + ",");
                                    }

                                    featsString.deleteCharAt(featsString.length() - 1);

                                    if (cmd.expects >= 0)
                                        featsString.append(" expect ").append(cmd.expects);
                                    int c= getLineStartOffset(temp.y - 1) + temp.x - 1;
                                    int d = getLineStartOffset(temp.y2 - 1) + temp.x2 - 1;
                                    changeText(c+1,d+1,featsString.toString());
                                }
                            });
                        }
                    }
                }

                pop.show(pane, x, y);
                }
            }

            /**
             * change integer to colorful annotation
             * @param i
             * @return
             */
            private String getColorString(Integer i) {
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
                return color;
            }
            private String getComandColorString(Set<Integer> key) {
                String name="";
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

                    name=name==""? color : name+","+color;
                }
                return name;
            }
        });

        component.addFocusListener(new FocusAdapter() {

            @Override
            public void focusGained(FocusEvent e) {
                pane.requestFocusInWindow();
            }
        });
        component.setFocusable(false);
        component.setMinimumSize(new Dimension(50, 50));
        component.setViewportView(pane);
        modified = false;
    }

    private boolean inWord(char c) {
        return Character.isAlphabetic(c) || Character.isDigit(c) || Character.isIdentifierIgnorable(c) || Character.isJavaIdentifierPart(c) || c == '\'' || c == '"';
    }

    boolean isValidSelection(String text, int start, int end) {
        return start >= 0 && start <= end && end >= start && end <= text.length();
    }

    String getCurrentWord() {
        String text = pane.getText();
        int[] selection = getCurrentWordSelection(text);
        if (selection == null)
            return null;

        return text.substring(selection[0], selection[1]);
    }

    int[] getCurrentWordSelection(String text) {

        int selectionStart = pane.getSelectionStart();
        int selectionEnd = pane.getSelectionEnd();

        if (!isValidSelection(text, selectionStart, selectionEnd))
            return null;

        while (isValidSelection(text, selectionStart - 1, selectionEnd) && inWord(text.charAt(selectionStart - 1)))
            selectionStart--;

        while (isValidSelection(text, selectionStart, selectionEnd + 1) && inWord(text.charAt(selectionEnd)))
            selectionEnd++;

        if (!isValidSelection(text, selectionStart, selectionEnd))
            return null;
        return new int[] {
                          selectionStart, selectionEnd
        };
    }

    private AbstractAction getSelectWordAction() {
        return new AbstractAction("select-word") {

            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                String text = pane.getText();
                int[] selection = getCurrentWordSelection(text);
                if (selection == null)
                    return;

                pane.setSelectionStart(selection[0]);
                pane.setSelectionEnd(selection[1]);

            }
        };
    }

    private void doTabInsert() {
        String s = pane.getSelectedText();
        if (s != null && s.length() > 0) {
            StringBuilder sb = new StringBuilder(s);
            sb.insert(0, '\t');
            for (int i = 1; i < sb.length() - 1; i++) {
                char c = sb.charAt(i);
                if (c == '\n') {
                    sb.insert(++i, '\t');
                }
            }
            replaceSelection(sb);
        } else {
            try {
                pane.getDocument().insertString(pane.getCaretPosition(), "\t", null);
            } catch (BadLocationException e1) {
                throw new RuntimeException(e1);
            }
        }
        listeners.fire(this, Event.CARET_MOVED);
    }
//colorful merge
    public JScrollPane getComponent(){
        return component;
    }
    private void doTabRemove() {
        String s = pane.getSelectedText();
        if (s != null && s.length() > 0) {
            StringBuilder sb = new StringBuilder(s);
            if (sb.charAt(0) == '\t')
                sb.delete(0, 1);

            for (int i = 1; i < sb.length() - 1; i++) {
                char c = sb.charAt(i);
                if (c == '\n' && sb.charAt(i + 1) == '\t') {
                    sb.delete(i + 1, i + 2);
                }
            }
            replaceSelection(sb);
        }
        listeners.fire(this, Event.CARET_MOVED);
    }

    private void doComment() {
        String s = pane.getSelectedText();
        if (s != null && s.length() > 0) {
            StringBuilder sb = new StringBuilder(s);
            int i = 0;
            while (i < sb.length() - 1) {
                if (sb.charAt(i) == '/' && sb.charAt(i + 1) == '/') {
                    sb.delete(i, i + 2);
                } else {
                    sb.insert(i, "//");
                    i += 2;
                }
                while (i < sb.length() - 1) {
                    if (sb.charAt(i) == '\n') {
                        i++;
                        break;
                    }
                    i++;
                }
            }
            replaceSelection(sb);
        } else {
            try {
                pane.getDocument().insertString(pane.getCaretPosition(), "/", null);
            } catch (BadLocationException e1) {
                throw new RuntimeException(e1);
            }
        }
        listeners.fire(this, Event.CARET_MOVED);
    }

    private void doNav() {
        try {
            String text = pane.getText();
            int[] sel = getCurrentWordSelection(text);
            Pos pos = Pos.toPos(text, sel[0], sel[1]);
            if (pos == null)
                return;

            String currentWord = getCurrentWord();
            if (currentWord == null)
                return;

            CompModule module = getModule();
            if (module == null)
                return;

            Expr expr = module.find(pos);
            if (expr != null) {
                Clause clause = expr.referenced();
                if (clause != null) {
                    Pos where = clause.pos();
                    if (where.sameFile(module.pos()))
                        select(where);
                    else {
                        OurSyntaxWidget ow = parent.open(where);
                        if (ow != null) {
                            ow.select(where);
                        }
                    }
                }
            }
        } catch (Exception e) {
            // Ignore, this is a best effort thingy
        }
    }

    CompModule getModule() {
        try {
            A4Reporter reporter = new A4Reporter();
            CompModule module = this.module;
            if (module == null)
                module = CompUtil.parseEverything_fromString(reporter, getText());
            this.module = module;
            return module;
        } catch (Err e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

    private void replaceSelection(CharSequence sb) {
        int selectionStart = pane.getSelectionStart();
        pane.replaceSelection(sb.toString());
        pane.setSelectionStart(selectionStart);
        pane.setSelectionEnd(selectionStart + sb.length());
    }

    /** Add this object into the given container. */
    public void addTo(JComponent newParent, Object constraint) {
        newParent.add(component, constraint);
    }

    /** Returns true if this textbox is currently shaded. */
    boolean shaded() {
        return pane.getHighlighter().getHighlights().length > 0;
    }

    /** Remove all shading. */
    void clearShade() {
        pane.getHighlighter().removeAllHighlights();
    }

    /**
     * Shade the range of text from start (inclusive) to end (exclusive).
     */
    // [HASLab] colorful Alloy, whether to strike out
   public void shade(Color color, boolean strike, int start, int end) {
        int c = color.getRGB() & 0xFFFFFF;
        if (painter == null || (painter.color.getRGB() & 0xFFFFFF) != c)
            painter = new OurHighlighter(color, strike); // [HASLab] colorful Alloy, whether to strike out
        try {
            pane.getHighlighter().addHighlight(start, end, painter);
        } catch (Throwable ex) {} // exception is okay
    }

    //colorful merge
    public void appendText(String string){
        Document docs= pane.getDocument();
        try {
            docs.insertString(docs.getLength(), "\r\n\n"+string, pane.getCharacterAttributes());//对文本进行追加
            pane.repaint();
        } catch (BadLocationException e) {
            e.printStackTrace();
        }
        pane.repaint();
    }

    //colorful merge
    public void changeText( int c, int d) {
        pane.setSelectionStart(c);
        pane.setSelectionEnd(d);
       // String s1=pane.getSelectedText();
        String s=pane.getSelectedText().replaceAll("[^\\s]", " ")+" ";
        if(s.length()==2){
            s=s.substring(0,s.length()-1);
        }else{
            pane.setSelectionStart(d+1);
            pane.setSelectionEnd(d+1000);
            String temp=pane.getSelectedText();
            if(temp.replace("\\s*|\t|\r|\n","").startsWith(",")){
                for (int i=0;i<s.length();i++){
                    String subStr = temp.substring(i, i+1);
                    if(subStr.equals(",")){
                        s=s+" ";
                        break;
                    }else{
                        s=s+subStr;
                    }
                }
            }
        }
        try {
            doc.replace(c,s.length(),s,null);
        } catch (BadLocationException e) {
            e.printStackTrace();
        }
        pane.repaint();
    }
    //colorful merge
    public void changeText(int c, int d,String text) {
        pane.setSelectionStart(c);
        pane.setSelectionEnd(d);
        pane.replaceSelection(text);
        pane.repaint();
    }
    /** Returns the filename. */
    public String getFilename() {
        return filename;
    }

    /** Returns the modified-or-not flag. */
    public boolean modified() {
        return modified;
    }

    /**
     * Returns whether this textarea is based on an actual disk file.
     */
    public boolean isFile() {
        return isFile;
    }

    /**
     * Changes the font name, font size, and tab size for the document.
     */
    void setFont(String fontName, int fontSize, int tabSize) {
        if (doc != null)
            doc.do_setFont(fontName, fontSize, tabSize);
    }

    /** Enables or disables syntax highlighting. */
    void enableSyntax(boolean flag) {
        if (doc != null)
            doc.do_enableSyntax(flag);
    }

    /**
     * Return the number of lines represented by the current text (where partial
     * line counts as a line).
     * <p>
     * For example: count("")==1, count("x")==1, count("x\n")==2, and
     * count("x\ny")==2
     */
    public int getLineCount() {
        return doc.do_getLineCount();
    }

    /**
     * Return the starting offset of the given line (If "line" argument is too
     * large, it will return the last line's starting offset)
     * <p>
     * For example: given "ab\ncd\n", start(0)==0, start(1)==3, start(2...)==6. Same
     * thing when given "ab\ncd\ne".
     */
    public int getLineStartOffset(int line) {
        return doc.do_getLineStartOffset(line);
    }

    /**
     * Return the line number that the offset is in (If "offset" argument is too
     * large, it will just return do_getLineCount()-1).
     * <p>
     * For example: given "ab\ncd\n", offset(0..2)==0, offset(3..5)==1,
     * offset(6..)==2. Same thing when given "ab\ncd\ne".
     */
    public int getLineOfOffset(int offset) {
        return doc.do_getLineOfOffset(offset);
    }

    /** Returns true if we can perform undo right now. */
    public boolean canUndo() {
        return doc.do_canUndo();
    }

    /** Returns true if we can perform redo right now. */
    public boolean canRedo() {
        return doc.do_canRedo();
    }

    /** Perform undo if possible. */
    public void undo() {
        int i = doc.do_undo();
        if (i >= 0 && i <= pane.getText().length())
            moveCaret(i, i);
    }

    /** Perform redo if possible. */
    public void redo() {
        int i = doc.do_redo();
        if (i >= 0 && i <= pane.getText().length())
            moveCaret(i, i);
    }

    /** Clear the undo history. */
    public void clearUndo() {
        doc.do_clearUndo();
    }

    /** Return the caret position. */
    public int getCaret() {
        return pane.getCaretPosition();
    }

    /**
     * Select the content between offset a and offset b, and move the caret to
     * offset b.
     */
    public void moveCaret(int a, int b) {
        try {
            pane.setCaretPosition(a);
            pane.moveCaretPosition(b);
        } catch (Exception ex) {
            if (a != 0 || b != 0)
                moveCaret(0, 0);
        }
    }

    /** Return the entire text. */
    public String getText() {
        return pane.getText();
    }
    //colorful merge
    public String getText(Pos pos) throws BadLocationException {
        int c= getLineStartOffset(pos.y - 1) + pos.x - 1 ;
        int d = getLineStartOffset(pos.y2 - 1) + pos.x2 - 1-c;
        return pane.getText(c,d);
    }

    /**
     * Change the entire text to the given text (and sets the modified flag)
     */
    public void setText(String text) {
        pane.setText(text);
    }

    /** Copy the current selection into the clipboard. */
    public void copy() {
        pane.copy();
    }

    /** Cut the current selection into the clipboard. */
    public void cut() {
        pane.cut();
    }

    /** Paste the current clipboard content. */
    public void paste() {
        pane.paste();
    }

    /**
     * Discard all; if askUser is true, we'll ask the user whether to save it or not
     * if the modified==true.
     *
     * @return true if this text buffer is now a fresh empty text buffer
     */
    boolean discard(boolean askUser, Collection<String> bannedNames) {
        char ans = (!modified || !askUser) ? 'd' : OurDialog.askSaveDiscardCancel("The file \"" + filename + "\"");
        if (ans == 'c' || (ans == 's' && save(false, bannedNames) == false))
            return false;
        for (int i = 1;; i++)
            if (!bannedNames.contains(filename = Util.canon("Untitled " + i + ".als")))
                break;
        fileModifiedDate = -1;
        pane.setText("");
        clearUndo();
        modified = false;
        isFile = false;
        listeners.fire(this, Event.STATUS_CHANGE);
        return true;
    }

    /**
     * Discard current content then read the given file; return true if the entire
     * operation succeeds.
     */
    boolean load(String filename) {
        String x;
        try {
            x = Util.readAll(filename);
            fileModifiedDate = Util.getModifiedDate(filename);
        } catch (Throwable ex) {
            OurDialog.alert("Error reading the file \"" + filename + "\"");
            return false;
        }
        pane.setText(x);
        moveCaret(0, 0);
        clearUndo();
        modified = false;
        isFile = true;
        this.filename = filename;
        listeners.fire(this, Event.STATUS_CHANGE);
        return true;
    }

    /**
     * Discard (after confirming with the user) current content then reread from
     * disk file.
     */
    void reload() {
        if (!isFile)
            return; // "untitled" text buffer does not have a on-disk file to
                   // refresh from
        if (modified && !OurDialog.yesno("You have unsaved changes to \"" + filename + "\"\nAre you sure you wish to discard " + "your changes and reload it from disk?", "Discard your changes", "Cancel this operation"))
            return;
        String t;
        try {
            t = Util.readAll(filename);
            fileModifiedDate = Util.getModifiedDate(filename);
        } catch (Throwable ex) {
            OurDialog.alert("Cannot read \"" + filename + "\"");
            return;
        }
        if (modified == false && t.equals(pane.getText()))
            return; // no text change nor status change
        int c = pane.getCaretPosition();
        pane.setText(t);
        moveCaret(c, c);
        modified = false;
        listeners.fire(this, Event.STATUS_CHANGE);
    }

    /**
     * Save the current tab content to the file system, and return true if
     * successful.
     */
    boolean saveAs(String filename, Collection<String> bannedNames) {
        filename = Util.canon(filename);
        if (bannedNames.contains(filename)) {
            OurDialog.alert("The filename \"" + filename + "\"\nis already open in another tab.");
            return false;
        }
        try {
            Util.writeAll(filename, pane.getText());
        } catch (Throwable e) {
            OurDialog.alert("Error writing to the file \"" + filename + "\"");
            return false;
        }
        this.filename = Util.canon(filename); // a new file's canonical name may
                                             // change
        fileModifiedDate = Util.getModifiedDate(this.filename);
        if (fileModifiedDate == 0)
            fileModifiedDate = new Date().getTime();

        modified = false;
        isFile = true;
        listeners.fire(this, Event.STATUS_CHANGE);
        return true;
    }

    /**
     * Save the current tab content to the file system and return true if
     * successful.
     *
     * @param alwaysPickNewName - if true, it will always pop up a File Selection
     *            dialog box to ask for the filename
     */
    boolean save(boolean alwaysPickNewName, Collection<String> bannedNames) {
        String n = this.filename;
        if (alwaysPickNewName || isFile == false || n.startsWith(Util.jarPrefix())) {
            File f = OurDialog.askFile(false, null, ".als", ".als files");
            if (f == null)
                return false;
            n = Util.canon(f.getPath());
            if (f.exists() && !OurDialog.askOverwrite(n))
                return false;
        }

        if (isFile && n.equals(this.filename) && Util.getModifiedDate(this.filename) > fileModifiedDate) {
            if (!OurDialog.yesno("The file has been modified outside the editor.\n" + "Do you want to overwrite it anyway?")) {
                return false;
            }
        }

        if (saveAs(n, bannedNames)) {
            Util.setCurrentDirectory(new File(filename).getParentFile());
            return true;
        } else
            return false;
    }

    /** Transfer focus to this component. */
    public void requestFocusInWindow() {
        if (pane != null)
            pane.requestFocusInWindow();
    }

    public void select(Pos pos) {
        String doc = pane.getText();
        int[] selection = pos.toStartEnd(doc);
        if (selection == null)
            return;

        pane.setSelectionStart(selection[0]);
        pane.setSelectionEnd(selection[1]);
    }

    public String getTooltip(MouseEvent event) {
        try { int offset = pane.viewToModel(event.getPoint());
            CompModule module = getModule();
            if (module == null)
                return null;

            String text = pane.getText();
            Pos pos = Pos.toPos(text, offset, offset + 1);
            Expr expr = module.find(pos);
            if (expr instanceof ExprBad) {
                return expr.toString();
            }
            if (expr != null) {
                Clause referenced = expr.referenced();
                if (referenced != null) {
                    String s = referenced.explain();
                    String table = "<html><pre>" + s + "</pre></html>";
                    s = table.replaceAll("\n", "<br/>");
                    return s;
                } else if (expr instanceof ExprConstant) {
                    String token = pos.substring(text);
                    if (token != null) {
                        String match = expr.toString();
                        if (!Objects.equals(token, match))
                            return match;
                    }
                }/* else{//colorful merge
                    Pos col=findColor(expr,module,pos);
                    if(col!=null && col!=Pos.UNKNOWN){
                        System.out.println(col);
                        JPopupMenu popupMenu = new JPopupMenu();
                        JMenuItem remove = new JMenuItem("Remove");
                        popupMenu.add(remove);
                        int cha=getCaret();
                        popupMenu.show( this.pane, cha, cha);
                        remove.addActionListener(new AbstractAction() {
                            @Override
                            public void actionPerformed(ActionEvent e) {
                                int c = getLineStartOffset(col.y2 - 1) + col.x2 - 1;
                                int d= getLineStartOffset(col.y - 1) + col.x - 1;
                                changeText(c,c+1,"");
                                changeText(d,d+1,"");
                            }
                        });
                        return pos.toString();
                    }
                }*/
            }
        } catch (Exception e) {
             e.printStackTrace();
            // ignore compile errors etc.
        }
        return null;
    }
/*//colorful merge
    private Pos findColor(Expr expr, CompModule module, Pos pos) {
        boolean find=false;
        Pos col=null;
        Map<Integer,Set<Integer>> map=new HashMap<>();//<feature canbe removed, full feature set>
        Expr facts=module.getAllReachableFacts();

        if(facts instanceof ExprList)
        for(Expr f:((ExprList) facts).args){
            if(f.toString().equals("some none")){
                if(f instanceof ExprUnary && ((ExprUnary) f).op.equals(ExprUnary.Op.NOOP))
                    f=((ExprUnary) f).sub;
                if(f.color.entrySet().size()==2){
                    for(Integer i: f.color.keySet()){
                        for(Integer j: f.color.keySet()){
                            if(j==i) continue;
                            else{
                                Set temp=new HashSet<>();
                                temp.add(i);
                                temp.add(-j);
                                map.put(-j,temp);
                            }
                        }
                    }
                }
            }
        }

        VisitQuery<Pos> findColor = new VisitQuery<Pos>(){
            @Override
            public Pos visit(ExprBinary x) throws Err {

                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                    if(p!=null)
                        return p;
                }
                Pos left=visitThis(x.left);
                return left!=null? left: visitThis(x.right);
            }

            private Pos find(Expr x, Map.Entry<Integer, Pos> value, Pos pos) {
                Pos po=null;
                if(value.getValue().x==pos.x && value.getValue().y==pos.y||value.getValue().x2==pos.x2 && value.getValue().y2==pos.y2 ){
                    //计算

                    if(x.color.keySet().containsAll(map.get(value.getKey())))
                        return value.getValue();
                   else{
                   Integer a=value.getKey();
                  Set b=  map.get(a);
                  Set c=x.color.keySet();
                  boolean d= c.containsAll(b);
                    //is a feature of this Expr, but can not remove
                        return Pos.UNKNOWN;}

                }
                //not a feature of this expr
                return po;
            }

            @Override
            public Pos visit(ExprList x) throws Err {
                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                    if(p!=null)
                        return p;
                }
                for(Expr e: x.args){
                   Pos psub= visitThis(e);
                   if(psub !=null)
                       return psub;
                }
            return null;
            }

            @Override
            public Pos visit(ExprCall x) throws Err {
                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                    if(p!=null)
                        return p;
                }
                return super.visit(x);
            }

            @Override
            public Pos visit(ExprConstant x) throws Err {
                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                    if(p!=null)
                        return p;
                }
                return super.visit(x);
            }

            @Override
            public Pos visit(ExprITE x) throws Err {
                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                     if(p!=null)
                        return p;
                }
                Pos e=visitThis(x.left);
                return e==null?visitThis(x.right):e;
            }

            @Override
            public Pos visit(ExprLet x) throws Err {
                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                    if(p!=null)
                        return p;
                }
                return visitThis(x.sub);
            }

            @Override
            public Pos visit(ExprQt x) throws Err {
                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                    if(p!=null)
                        return p;
                }
                return visitThis(x.sub);
            }

            @Override
            public Pos visit(ExprUnary x) throws Err {
                for(Map.Entry<Integer, Pos> co:x.color.entrySet()){
                    Pos p=find(x,co,pos);
                   if(p!=null)
                        return p;
                }
                return visitThis(x.sub);
            }

            @Override
            public Pos visit(ExprVar x) throws Err {
                return null;
            }

            @Override
            public Pos visit(Sig x) throws Err {
                return null;
            }

            @Override
            public Pos visit(Sig.Field x) throws Err {
                return null;
            }
        };
       col= expr.accept(findColor);
        return col;
    }*/

    /** Retrieve the Pos of the selected text in the editor. */
    // [HASLab] colorful Alloy
    public Pos getPosSelected() {
        int y1 = 1 + getLineOfOffset(pane.getSelectionStart());
        int y2 = 1 + getLineOfOffset(pane.getSelectionEnd());
        int x1 = 1 + pane.getSelectionStart() - getLineStartOffset(y1 - 1);
        int x2 = pane.getSelectionEnd() - getLineStartOffset(y2 - 1);
        return new Pos(getFilename(), x1, y1, x2, y2);
    }

    /** A label view with the ability to strike out text with colors. */
    // [HASLab] colorful Alloy
    class StrekableLabellView extends LabelView {

        public StrekableLabellView(Element elem) {
            super(elem);
        }

        @Override
        public void paint(Graphics g, Shape allocation) {
            super.removeAll();
            super.paint(g, allocation);
            paintStrikeLine(g, allocation);
        }

        // [HASLab] colorful Alloy
        public void paintStrikeLine(Graphics g, Shape a) {
            Color c = (Color) getElement().getAttributes().getAttribute("strike-color");
            if (c != null) {
                int y = a.getBounds().y + a.getBounds().height - (int) getGlyphPainter().getDescent(this);

                y = y - (int) (getGlyphPainter().getAscent(this) * 0.5f);
                int x1 = (int) a.getBounds().getX();
                int x2 = (int) (a.getBounds().getX() + a.getBounds().getWidth());

                Color old = g.getColor();
                g.setColor(c);
                g.drawRect(x1, y, x2 - x1, 1);
                g.setColor(old);
            }
        }
    }

    /** The colors of each of the features. */
    // [HASLab] colorful Alloy
    public static Color C[] = {
                               new Color(255, 225, 205), new Color(255, 205, 225), new Color(205, 255, 225), new Color(225, 255, 205), new Color(225, 205, 255), new Color(205, 225, 255), new Color(225, 255, 225), new Color(225, 225, 255), new Color(255, 225, 225)
    };



}
