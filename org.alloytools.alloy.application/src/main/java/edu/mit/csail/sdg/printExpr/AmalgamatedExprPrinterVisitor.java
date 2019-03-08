package edu.mit.csail.sdg.printExpr;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;

import java.util.HashSet;
import java.util.Set;

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
        //left
        if(!x.left.color.isEmpty())
            str.append("(");
        str.append( visitThis(x.left));
        if(!x.left.color.isEmpty()){
            str.append(" else ");
            printElse(str, x.type().arity(), x);
            str.append(")");
        }

        str.append(x.op.getLabel()+" ");
        //-----print x.right ------
        if (!(x.right instanceof ExprUnary)||!(x.right.color.isEmpty()))
            str.append("(");
        str.append( visitThis(x.right));
        if(!x.right.color.isEmpty()){
            str.append(" else ");
            printElse(str, x.type().arity(), x);
        }
        if (!(x.right instanceof ExprUnary)||!(x.right.color.isEmpty()))
            str.append(")");


        str.append(")");
        return str.toString();
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
                    str.append(" "+visitThis(arg));
                    str.append(" "+x.op.name());
                }

            }

            if(!PFeatures.isEmpty()){
                //F in Product implies
                str.append("(");
                addFeatureprefix(PFeatures,str, "in","and");

                for(Expr arg: x.args){
                    str.append(" "+visitThis(arg));
                    str.append(" "+x.op.name());
                }
            }

            str.deleteCharAt(str.length()-1);
            str.deleteCharAt(str.length()-1);
            if(x.op.equals(ExprList.Op.AND))
                str.deleteCharAt(str.length()-1);
            str.append(")");
        }


//--------------------x.argi (i=0,1,2,3)----------------
        for(Expr arg: x.args){
            str.append("\r\n    ");
            if(arg.color.isEmpty()){
                str.append(visitThis(arg));
            }else{
                // x not marked but arg i marked
                Set<Integer> NFeaturessub=new HashSet<>();
                Set<Integer> PFeaturessub=new HashSet<>();
                for(Integer i: x.color){
                    if(i<0)
                        NFeaturessub.add(-i);
                    else PFeaturessub.add(i);
                }
                str.append("(");
                str.append(visitThis(arg));
                // str.append(" else ");
                //printElse(str,x);
                str.append(")");
            }
            String name=x.op.name();
            if(name.equals("AND")) name="and";
            if(name.equals("OR")) name="or";
            str.append(name);
        }

        // delete the last "or" or "and" string
        str.deleteCharAt(str.length()-1);
        str.deleteCharAt(str.length()-1);

        if(x.op.equals(ExprList.Op.AND))
            str.deleteCharAt(str.length()-1);
        return str.toString();
    }

    @Override
    public String visit(ExprCall x) throws Err {

        StringBuilder str=new StringBuilder();

        StringBuilder tempExpr =new StringBuilder();
        tempExpr.append(x.fun.label.substring(x.fun.label.indexOf("/")+1));
        if(x.args.size()>0) {
            tempExpr.append("[");
            for (Expr arg : x.args) {
                tempExpr.append(visitThis(arg) + ",");
            }

            tempExpr.deleteCharAt(tempExpr.length() - 1);
            tempExpr.append("]");
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


        str.append(visitThis(x.var));
        str.append("=");

        str.append(visitThis(x.expr));
        return str.toString();

    }

    @Override
    public String visit(ExprQt x) throws Err {
        StringBuilder str=new StringBuilder();

        StringBuilder tempExpr=new StringBuilder();

        if(!x.op.equals(ExprQt.Op.COMPREHENSION))
            //all
            tempExpr.append(x.op.getLabel() +" ");



        for (Decl decl :x.decls){
            for (Expr e: decl.names){
                tempExpr.append(visitThis(e)+" ,");
            }
            tempExpr.deleteCharAt(str.length() - 1);
            tempExpr.append(": ");
            tempExpr.append(visitThis(decl.expr)+",");
        }
        tempExpr.deleteCharAt(str.length()-1);

        tempExpr.append("|");

        tempExpr.append(visitThis(x.sub));


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
        if(x.op.equals(ExprUnary.Op.SOMEOF))
            tempExpr.append(" some ");
        if(x.op.equals(ExprUnary.Op.LONEOF))
            tempExpr.append(" lone ");
        if(x.op.equals(ExprUnary.Op.ONEOF))
            tempExpr.append(" ");
        if(x.op.equals(ExprUnary.Op.EXACTLYOF))
            tempExpr.append(" exactly ");
        if(x.op.equals(ExprUnary.Op.NOT)||x.op.equals(ExprUnary.Op.NO)||
                x.op.equals(ExprUnary.Op.SOME)||x.op.equals(ExprUnary.Op.ONE)||
                x.op.equals(ExprUnary.Op.LONE)||x.op.equals(ExprUnary.Op.TRANSPOSE)||
                x.op.equals(ExprUnary.Op.RCLOSURE)||x.op.equals(ExprUnary.Op.CLOSURE)||
                x.op.equals(ExprUnary.Op.CARDINALITY))
            tempExpr.append(" "+x.op.getOpLabel()+" ");
        tempExpr.append(visitThis(x.sub));


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
        return str.toString();
    }

    @Override
    public String visit(ExprVar x) throws Err {

        // StringBuilder str=new StringBuilder();
        // if(!x.color.isEmpty())
        // addFeatureprefix(str, x);
        // str.append(x.label);

        return " "+x.label+ " ";

    }

    @Override
    public String visit(Sig x) throws Err {
        return x.label.substring(5)+" ";
    }

    @Override
    public String visit(Sig.Field x) throws Err {
        return x.label+" ";
    }
    /**
     * for ExprList "and","or" operator
     * @param str
     * @param x
     *
     */

    private void printElse(StringBuilder str, int arity,ExprBinary x) {

        //    + operator
        if(x.op.equals(ExprBinary.Op.PLUS))
            printElseString(str,arity," none ");
        //   & operator
        if(x.op.equals(ExprBinary.Op.INTERSECT))
            printElseString(str,arity," univ ");
    }


    private void printElseString(StringBuilder str, int arity, String string) {
        StringBuilder elseString=new StringBuilder();
        for (int i=0; i< arity;i++){
            elseString.append( " "+string+" " +"->");
        }
        elseString.deleteCharAt(elseString.length()-1);
        elseString.deleteCharAt(elseString.length()-1);
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

    private void addFeatureprefix(Set<Integer> PFeature,StringBuilder str, String inOrNot,String operator) {

        for (Integer i: PFeature){

            str.append(" F"+i + " "+inOrNot+" Product "+operator);
        }
    }

}
