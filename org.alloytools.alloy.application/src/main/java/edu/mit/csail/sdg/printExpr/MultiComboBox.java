package edu.mit.csail.sdg.printExpr;
/**
 * Generate Feature selected Button, ( 1-0 feature buttons and  "Execute", "FModule", "UModule" button at bottom)
 */

import javax.swing.*;
import javax.swing.plaf.basic.BasicArrowButton;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class MultiComboBox extends JComponent {
    public static Set<Integer> selectedFeatures;

    private Object[] values;

    public Object[] defaultValues;

    private List<ActionListener> listeners = new ArrayList<ActionListener>();

    public MultiPopup popup;

    private JTextField editor;

    protected JButton   arrowButton;

    private String valueSperator;

    private static final String DEFAULT_VALUE_SPERATOR = ",";

    public MultiComboBox(Object[] value, Object[] defaultValue){
        this(value,defaultValue,DEFAULT_VALUE_SPERATOR);
    }

    public MultiComboBox(Object[] value, Object[] defaultValue , String valueSperator) {
        values = value;
        defaultValues = defaultValue;
        this.valueSperator = valueSperator;
        initComponent();
    }

    private void initComponent() {

        this.setBackground(Color.red);
        this.setLayout(new FlowLayout());
        popup =new  MultiPopup(values,defaultValues);
        popup.addActionListener(new PopupAction());
        editor = new JTextField();
        editor.setBackground(Color.white);
        editor.setEditable(false);
        editor.setPreferredSize(new Dimension(150,20));

        editor.addMouseListener(new EditorHandler());
        arrowButton = createArrowButton();
        arrowButton.addMouseListener(new EditorHandler());
        add(editor);
        add(arrowButton);
        setText();
        //editor.setText("Selected features");


        selectedFeatures=new HashSet<Integer>(){{
            add(1);
            add(2);
            add(3);
            add(4);
            add(5);
            add(6);
            add(7);
            add(8);
            add(9);
            add(0); }
        };
    }

    public Object[] getSelectedValues() {

        return popup.getSelectedValues();
    }



    public void addActionListener(ActionListener listener) {
        if (!listeners.contains(listener))
            listeners.add(listener);
    }



    protected void fireActionPerformed(ActionEvent e) {
        for (ActionListener l : listeners) {
            l.actionPerformed(e);
        }
    }

    private class PopupAction implements ActionListener{

        public void actionPerformed(ActionEvent e) {

            if(e.getActionCommand().equals(MultiPopup.CANCEL_EVENT)){

            }else if(e.getActionCommand().equals(MultiPopup.PROJECT_FEATURE_EVENT)){
                defaultValues = popup.getSelectedValues();
                setText();

                //
                fireActionPerformed(e);
            }else if(e.getActionCommand().equals(MultiPopup.Executed_EVENT)){
                defaultValues = popup.getSelectedValues();
                setText();

                //
                fireActionPerformed(e);
            }else if(e.getActionCommand().equals(MultiPopup.UnionModule_Event)){

                defaultValues = popup.getSelectedValues();
                setText();

                //
                fireActionPerformed(e);
            }
            togglePopup();


        }

    }

    private void togglePopup(){
        if(popup.isVisible()){
            popup.setVisible(false);
        }else{
            popup.setDefaultValue(defaultValues);
            popup.show(this, 0, getHeight());
        }
    }

    private void setText() {
        StringBuilder builder = new StringBuilder();
        for(Object dv : defaultValues){
            builder.append(dv);
            builder.append(valueSperator);
        }

        editor.setText(builder.substring(0, builder.length() > 0 ? builder.length() -1  : 0).toString());
    }

    private class EditorHandler implements MouseListener{

        public void mouseClicked(MouseEvent e) {
            togglePopup();
        }

        public void mousePressed(MouseEvent e) {

        }

        public void mouseReleased(MouseEvent e) {

        }

        public void mouseEntered(MouseEvent e) {

        }

        public void mouseExited(MouseEvent e) {

        }

    }


    public void paintComponent(Graphics g){
        g.setColor(Color.white);
        g.fillRect(0,0,getWidth(),getHeight());
    }


    protected JButton createArrowButton() {
        JButton button = new BasicArrowButton(BasicArrowButton.SOUTH,
                UIManager.getColor("ComboBox.buttonBackground"),
                UIManager.getColor("ComboBox.buttonShadow"),
                UIManager.getColor("ComboBox.buttonDarkShadow"),
                UIManager.getColor("ComboBox.buttonHighlight"));
        button.setName("ComboBox.arrowButton");
        return button;
    }



}
