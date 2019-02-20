package edu.mit.csail.sdg.printExpr;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.List;

public class MultiPopup extends JPopupMenu {

    private List<ActionListener> listeners = new ArrayList<ActionListener>();

    private Object[] values;

    private Object[] defaultValues;

    private List<JCheckBox> checkBoxList = new ArrayList<JCheckBox>();

    public JButton selectedModuleButton;

    public JButton cancelButton;
    public JButton executeButton;


    public static final String PROJECT_FEATURE_EVENT = "commit";

    public static final String CANCEL_EVENT = "cancel";
    public static final String Executed_EVENT = "execute";
    public static  final String UnionModule_Event ="enumerative";

    public MultiPopup(Object[] value , Object[] defaultValue) {
        super();
        values = value;
        defaultValues = defaultValue;
        initComponent();
    }

    public void addActionListener(ActionListener listener) {
        if (!listeners.contains(listener))
            listeners.add(listener);
    }



    private void initComponent() {

        JPanel checkboxPane = new JPanel();

        JPanel buttonPane = new JPanel();

        this.setLayout(new BorderLayout());


        for(Object v : values){
            JCheckBox temp = new JCheckBox(v.toString() , selected(v));
            checkBoxList.add(temp);
        }

        checkboxPane.setLayout(new GridLayout(checkBoxList.size() , 1 ,3, 3));
        for(JCheckBox box : checkBoxList){
            checkboxPane.add(box);
        }

        selectedModuleButton = new JButton("Code");

        selectedModuleButton.addActionListener(new ActionListener(){

            public void actionPerformed(ActionEvent e) {
                commit();
            }

        });

        cancelButton = new JButton("Cancel");

        cancelButton.addActionListener(new ActionListener(){

            public void actionPerformed(ActionEvent e) {
                cancel();
            }

        });



        executeButton = new JButton("Execute");

        executeButton.addActionListener(new ActionListener(){

            public void actionPerformed(ActionEvent e) {
                execute();
            }

        });


        //buttonPane.add(cancelButton);

        buttonPane.add(executeButton);
        buttonPane.add(selectedModuleButton);

        this.add(checkboxPane , BorderLayout.CENTER);

        this.add(buttonPane , BorderLayout.SOUTH);


    }

    private boolean selected(Object v) {
        for(Object dv : defaultValues){
            if( dv .equals(v) ){
                return true;
            }
        }
        return false;
    }

    protected void fireActionPerformed(ActionEvent e) {
        for (ActionListener l : listeners) {
            l.actionPerformed(e);
        }
    }

    public Object[] getSelectedValues(){
        List<Object> selectedValues = new ArrayList<Object>();


            for(int i = 0 ; i < checkBoxList.size() ; i++){

                if(checkBoxList.get(i).isSelected())
                    selectedValues.add(values[i]);
            }


        return selectedValues.toArray(new Object[selectedValues.size()]);
    }

    public void setDefaultValue(Object[] defaultValue) {
        defaultValues = defaultValue;

    }

    public void commit(){
        fireActionPerformed(new ActionEvent(this, 0, PROJECT_FEATURE_EVENT));
    }

    public void cancel(){
        fireActionPerformed(new ActionEvent(this, 0, CANCEL_EVENT));
    }
    public void execute(){
        fireActionPerformed(new ActionEvent(this, 0, Executed_EVENT));
    }




}
