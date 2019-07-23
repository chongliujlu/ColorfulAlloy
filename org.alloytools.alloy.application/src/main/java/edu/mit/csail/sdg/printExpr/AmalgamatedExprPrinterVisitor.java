package edu.mit.csail.sdg.printExpr;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;

import java.util.HashSet;
import java.util.Set;

/**
 * This class implements a visitor that print the expressions for the Amalgamated approach.
 */
public class AmalgamatedExprPrinterVisitor extends VisitReturn<String> {

    @Override
    public String visit(ExprBinary x) throws Err {
        //only for + ,&  operator

        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }

        StringBuilder str=new StringBuilder();
       // if (x.color.isEmpty())
       // if(x.color.isEmpty() &&((! x.op.equals(ExprBinary.Op.JOIN)|| (x.op.equals(ExprBinary.Op.JOIN) && x.right instanceof ExprCall))))
            str.append("(");


        if(!NFeatures.isEmpty()){
            if(x.color.size()>1)
                str.append("(");
            addFeatureprefix(NFeatures,str, "not in","and");
            if(PFeatures.isEmpty()) {
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);

                if(x.color.size()>1)
                    str.append(")");
                str.append(" implies (");
            }

        }
        if(!PFeatures.isEmpty()){
           // if(x.color.size()>1&& NFeatures.isEmpty())
            //    str.append("(");
            addFeatureprefix(PFeatures,str, "in","and");
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.color.size()>1)
                str.append(")");
            str.append(" implies (");
        }
        //left
        //if(!x.left.color.isEmpty())
         //   str.append("(");
        str.append( visitThis(x.left));

        if(!x.left.color.isEmpty()){
            if(!(x.left instanceof ExprBinary)) {
                str.deleteCharAt(str.length()-1);
                str.append(" else ");
                printElse(str, x.type().arity(), x);
                str.append(")");
            }else if(x.op.equals(ExprBinary.Op.INTERSECT)){
                deletenone(str,x.left.type().arity());
                printElse(str, x.left.type().arity(), x);
                str.append(")");
            }

        }

        if(x.op.equals(ExprBinary.Op.JOIN))
            str.append(x.op.getLabel());
         else
            str.append(" "+x.op.getLabel()+" ");
        //-----print x.right ------
      //  if (!(x.right.color.isEmpty()))
         //   str.append("(");

        str.append( visitThis(x.right));

        if(!x.right.color.isEmpty()){
            if(!(x.right instanceof ExprBinary)) {
                str.deleteCharAt(str.length()-1);
                str.append(" else ");
                printElse(str, x.right.type().arity(), x);
                str.append(")");
            }else if(x.op.equals(ExprBinary.Op.INTERSECT)){
                deletenone(str,x.right.type().arity());
                printElse(str, x.right.type().arity(), x);
                str.append(")");

            }

        }


        // implies (
        if(!x.color.isEmpty()){
            str.append(")");
            if(x.type().arity()>0){
                str.append(" else ");
                printElse(str, x.type().arity());
            }
            str.append(")");
        }



        if(x.color.isEmpty())
        //if(x.color.isEmpty() &&((! x.op.equals(ExprBinary.Op.JOIN)|| (x.op.equals(ExprBinary.Op.JOIN) && x.right instanceof ExprCall))))
            str.append(")");
        return str.toString();
    }

    private void deletenone(StringBuilder str, int arity) {

        StringBuilder elseString=new StringBuilder();
        for (int i=0; i< arity;i++){
            elseString.append( " "+" none "+" " +"->");
        }
        if(elseString.length()>1){
            elseString.deleteCharAt(elseString.length()-1);
            elseString.deleteCharAt(elseString.length()-1);
        }
        str.delete(str.length()-1-elseString.length(),str.length());

    }

    @Override
    public String visit(ExprList x) throws Err {

        StringBuilder str=new StringBuilder();

        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }


        //x marked
        if(!x.color.isEmpty()){
            //Marked with NFeature
            if(!NFeatures.isEmpty()){
                str.append("(");
                addFeatureprefix(NFeatures,str, "not in","and");

                for(Expr arg: x.args){
                   String subExpr= visitThis(arg);
                   if(x.op.equals(ExprList.Op.OR)){
                       // marked with A or ➀B➀ , A and (F1 in Product and B)
                       subExpr=subExpr.replaceAll("implies","and");
                       str.append("("+subExpr+")");
                   }
                    else str.append(" "+subExpr);
                    str.append(" "+x.op.name());
                }

            }

            if(!PFeatures.isEmpty()){
                //F in Product implies
                str.append("(");
                addFeatureprefix(PFeatures,str, "in","and");
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                //if(x.op.equals(ExprList.Op.AND))
                    str.deleteCharAt(str.length()-1);
                str.append(")");
                str.append(" implies ");

            }
        }

//--------------------x.argi (i=0,1,2,3)----------------
        String name=x.op.name();
        if(name.equals("AND")) name=" and";
        if(name.equals("OR")) name=" or";

        if(!x.args.isEmpty())
            str.append("(");

        for(Expr arg: x.args){
            String subExpr= visitThis(arg);

            if(x.op.equals(ExprList.Op.OR) && !(arg.color.isEmpty())){
                //subExpr=subExpr.replaceAll("implies","and");
                if(subExpr.endsWith("]"))
                    str.append("("+subExpr +" else some none)");
                else
                str.append("("+subExpr.substring(0,subExpr.length()-1) +" else some none))");
            }
            else
                str.append("("+subExpr+")");
            str.append(name);
            str.append("\r\n        ");

        }

        // delete the last "or" or "and" string
        str.delete(str.length()-13,str.length()-1);

        if(x.op.equals(ExprList.Op.AND))
            str.deleteCharAt(str.length()-1);

        if(!x.args.isEmpty())
            str.append(")");
        return str.toString();
    }

    @Override
    public String visit(ExprCall x) throws Err {

        StringBuilder str=new StringBuilder();

        StringBuilder tempExpr =new StringBuilder();

        //if(x.args.size()>0)
       // if(x.fun.label.substring(x.fun.label.indexOf("/")+1).equals("prev")||x.fun.label.substring(x.fun.label.indexOf("/")+1).equals("prevs"))
        //    tempExpr.append("(");
        String name= x.fun.label;
        while (name.contains("/")){
            name=name.substring(name.indexOf("/")+1);
        }
        tempExpr.append(name);
       // tempExpr.append(x.fun.label.substring(x.fun.label.indexOf("/")+1));
        if(x.args.size()>0) {
            tempExpr.append("[");
            for (Expr arg : x.args) {
                tempExpr.append(visitThis(arg) + ",");
            }

            tempExpr.deleteCharAt(tempExpr.length() - 1);
            tempExpr.append("]");
          //  if(x.fun.label.substring(x.fun.label.indexOf("/")+1).equals("prev")||x.fun.label.substring(x.fun.label.indexOf("/")+1).equals("prevs"))
            //    tempExpr.append("(");
        }

        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }
        if(!NFeatures.isEmpty()){
            if(x.color.size()>1)
                str.append("(");
            addFeatureprefix(NFeatures,str, "not in","and");
            if(PFeatures.isEmpty()) {
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);

                if(x.color.size()>1)
                    str.append(")");
                str.append(" implies ");
            }

        }
        if(!PFeatures.isEmpty()){
            if(x.color.size()>1&& NFeatures.isEmpty())
                str.append("(");
            addFeatureprefix(PFeatures,str, "in","and");
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.color.size()>1)
                str.append(")");
            str.append(" implies ");
        }

            str.append(tempExpr);

        return str.toString();

    }

    @Override
    public String visit(ExprConstant x) throws Err {
        StringBuilder str=new StringBuilder();
        StringBuilder tempExpr =new StringBuilder();


        if(x.op.equals(ExprConstant.Op.TRUE))
            tempExpr.append( " true ");
        if(x.op.equals(ExprConstant.Op.FALSE))
            tempExpr.append( " false ");
        if(x.op.equals(ExprConstant.Op.IDEN))
            tempExpr.append(" iden ");

        if(x.op.equals(ExprConstant.Op.MAX))
            tempExpr.append(" fun/max ");
        if(x.op.equals(ExprConstant.Op.MIN))
            tempExpr.append(" fun/min ");
        if(x.op.equals(ExprConstant.Op.NEXT))
            tempExpr.append( " fun/next ");
        if(x.op.equals(ExprConstant.Op.EMPTYNESS))
            tempExpr.append( " none ");
        if(x.op.equals(ExprConstant.Op.STRING))
            tempExpr.append( " " + x.string+" ");
        if(x.op.equals(ExprConstant.Op.NUMBER))
            tempExpr.append( " " + x.num+" ");


        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }
        if(!NFeatures.isEmpty()){
            if(x.color.size()>1)
                str.append("(");
            addFeatureprefix(NFeatures,str, "not in","and");
            if(PFeatures.isEmpty()) {
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);

                if(x.color.size()>1)
                    str.append(")");
                str.append(" implies ");
            }

        }
        if(!PFeatures.isEmpty()){
            if(x.color.size()>1&& NFeatures.isEmpty())
                str.append("(");
            addFeatureprefix(PFeatures,str, "in","and");
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.color.size()>1)
                str.append(")");
            str.append(" implies ");
        }

        str.append(tempExpr);

        return str.toString();
    }

    @Override
    public String visit(ExprITE x) throws Err {
        StringBuilder str=new StringBuilder();
        str.append("(");

        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }
        if(!NFeatures.isEmpty()){
            if(x.color.size()>1)
                str.append("(");
            addFeatureprefix(NFeatures,str, "not in","and");
            if(PFeatures.isEmpty()) {
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);

                if(x.color.size()>1)
                    str.append(")");
                str.append(" implies ");
            }

        }
        if(!PFeatures.isEmpty()){
            if(x.color.size()>1&& NFeatures.isEmpty())
                str.append("(");
            addFeatureprefix(PFeatures,str, "in","and");
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.color.size()>1)
                str.append(")");
            str.append(" implies ");
        }

        str.append(visitThis(x.cond));
        str.append(" implies ");

        str.append(visitThis(x.left));
        str.append(" else ");
        str.append(visitThis(x.right));

        str.append(")");

        return str.toString();
    }

    @Override
    public String visit(ExprLet x) throws Err {
        StringBuilder str=new StringBuilder();

        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }
        if(!NFeatures.isEmpty()){
            if(x.color.size()>1)
                str.append("(");
            addFeatureprefix(NFeatures,str, "not in","and");
            if(PFeatures.isEmpty()) {
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);

                if(x.color.size()>1)
                    str.append(")");
                str.append(" implies ");
            }

        }
        if(!PFeatures.isEmpty()){
            if(x.color.size()>1&& NFeatures.isEmpty())
                str.append("(");
            addFeatureprefix(PFeatures,str, "in","and");
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.color.size()>1)
                str.append(")");
            str.append(" implies ");
        }

        str.append("(");
        str.append("let ");
        str.append(visitThis(x.var));
        str.append("=");

        str.append(visitThis(x.expr));
        str.append(" | ");
        str.append(visitThis(x.sub));
        str.append(")");

        //if(!x.color.isEmpty())
         //   str.append(" else none ");
        return str.toString();

    }

    @Override
    public String visit(ExprQt x) throws Err {
        StringBuilder str=new StringBuilder();

        StringBuilder tempExpr=new StringBuilder();
        tempExpr.append("{");
        if(!x.op.equals(ExprQt.Op.COMPREHENSION))
            //all，no
            tempExpr.append(x.op.getLabel() +" ");

        for (Decl decl :x.decls){
            if(decl.disjoint!=null)
                tempExpr.append( " disj "); //"disj" key word
            for (Expr e: decl.names){
                tempExpr.append(visitThis(e)+",");
            }
            tempExpr.deleteCharAt(tempExpr.length() - 1);
            tempExpr.append(": ");
            tempExpr.append(visitThis(decl.expr)+",");
        }

        tempExpr.deleteCharAt(tempExpr.length()-1);
        tempExpr.append(" | ");
        tempExpr.append(visitThis(x.sub));
        tempExpr.append("}");


        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }
        if(!x.color.isEmpty())
            str.append("(");

        if(!NFeatures.isEmpty()){

            if(x.color.size()>1)
                str.append("(");

            addFeatureprefix(NFeatures,str, "not in","and");
            if(PFeatures.isEmpty()) {
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);

                if(x.color.size()>1)
                    str.append(")");
                str.append(" implies ");
            }

        }
        if(!PFeatures.isEmpty()){
            if(x.color.size()>1&& NFeatures.isEmpty())
                str.append("(");
            addFeatureprefix(PFeatures,str, "in","and");
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.color.size()>1)
                str.append(")");
            str.append(" implies ");
        }
            str.append(tempExpr);

            if(!x.color.isEmpty())
                str.append(")");

        return str.toString();
    }

    @Override
    public String visit(ExprUnary x) throws Err {
        Set<Integer> NFeatures=new HashSet<>();
        Set<Integer> PFeatures=new HashSet<>();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }

        StringBuilder str=new StringBuilder();

        StringBuilder tempExpr= new StringBuilder();
        if(x.op.equals(ExprUnary.Op.SETOF))
            tempExpr.append(" set ");
        else if(x.op.equals(ExprUnary.Op.SOMEOF))
            tempExpr.append(" some ");
        else if(x.op.equals(ExprUnary.Op.LONEOF))
            tempExpr.append(" lone ");
        else if(x.op.equals(ExprUnary.Op.ONEOF))
            tempExpr.append(" one ");
        else if(x.op.equals(ExprUnary.Op.EXACTLYOF))
            tempExpr.append(" exactly ");
        else if(x.op.equals(ExprUnary.Op.RCLOSURE)||x.op.equals(ExprUnary.Op.CLOSURE)||
                x.op.equals(ExprUnary.Op.CARDINALITY))
            tempExpr.append(" "+x.op.getOpLabel()+"("); // (

        else if(x.op.equals(ExprUnary.Op.NOT)||x.op.equals(ExprUnary.Op.NO)||
                x.op.equals(ExprUnary.Op.SOME)||x.op.equals(ExprUnary.Op.ONE)||
                x.op.equals(ExprUnary.Op.LONE)||x.op.equals(ExprUnary.Op.TRANSPOSE))
            tempExpr.append(" "+x.op.getOpLabel()+" ");
        tempExpr.append(visitThis(x.sub));

        if(x.op.equals(ExprUnary.Op.RCLOSURE)||x.op.equals(ExprUnary.Op.CLOSURE)||
                x.op.equals(ExprUnary.Op.CARDINALITY))
            tempExpr.append(")");  // )

        if(!x.color.isEmpty())
             str.append("(");

        if(!NFeatures.isEmpty()){
            if(x.color.size()>1)
                str.append("(");
            addFeatureprefix(NFeatures,str, "not in","and");
            if(PFeatures.isEmpty()) {
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);
                str.deleteCharAt(str.length()-1);

                if(x.color.size()>1)
                    str.append(")");
                str.append(" implies ");
            }

        }
        if(!PFeatures.isEmpty()){
            if(x.color.size()>1 && NFeatures.isEmpty())
                str.append("(");
            addFeatureprefix(PFeatures,str, "in","and");
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.color.size()>1)
                str.append(")");
            str.append(" implies ");
        }

        str.append(tempExpr);
       if (!(x.color.isEmpty())){
           str.append(")");

       }

        return str.toString();
    }

    @Override
    public String visit(ExprVar x) throws Err {
        return " "+x.label+ " ";
    }

    @Override
    public String visit(Sig x) throws Err {
        if(x.label.contains("/")){
           return x.label.substring(x.label.indexOf("/")+1);
        }
        return x.label;
    }

    @Override
    public String visit(Sig.Field x) throws Err {
        return x.label+" ";
    }

    /**
     * help method, used to print the else clause for ExprList "and","or" operator
     * @param str to add the else string
     * @param x The binary expression marked with features
     */
    private void printElse(StringBuilder str, int arity,ExprBinary x) {
        //    + operator
        if(x.op.equals(ExprBinary.Op.PLUS))
            printElseString(str,arity," none ");
        //   & operator
        else if(x.op.equals(ExprBinary.Op.INTERSECT))
            printElseString(str,arity," univ ");
        else
            //for example  .
            printElseString(str,arity," none ");
    }

    /**
     * help method, used to print the else clause
     * @param str  to add the else string
     * @param arity The arity of the expression
     */
    private void printElse(StringBuilder str, int arity) {
            printElseString(str,arity," none ");
    }

    /**
     * help method, used to print the else clause
     * @param str  to add the else string
     * @param arity aritity of the expression marked with features
     * @param string String to be printed
     *         for example, arity =2, string =none, the string to be add to str will be "none->none"
     */
    private void printElseString(StringBuilder str, int arity, String string) {
        StringBuilder elseString=new StringBuilder();
        for (int i=0; i< arity;i++){
            elseString.append( " "+string+" " +"->");
        }
        if(elseString.length()>1){
            elseString.deleteCharAt(elseString.length()-1);
            elseString.deleteCharAt(elseString.length()-1);
        }
        str.append(elseString);
    }

    /**
     *help methord, print the prefix for the expressions that marked with features
     *
     * @param PFeature the features marked,
     * @param str to add the prifix
     * @param inOrNot string "in " or "not in "
     * @param operator "and" or "or"
     *for examples, marked with ➊,➁
     */
    private void addFeatureprefix(Set<Integer> PFeature,StringBuilder str, String inOrNot,String operator) {
        for (Integer i: PFeature){
            str.append(" _F"+i + " "+inOrNot+" _Product_ "+operator);
        }
    }

}
