package edu.mit.csail.sdg.printExpr;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;

/**
 *  print readable string for and Expr
 */
public  class ExprPrinterVisitor extends VisitReturn<String> {
    @Override
    public String visit(ExprBinary x) throws Err {

        String left=visitThis(x.left);
        String right =visitThis(x.right);
        if (left.equals("") )
            return right;
        else if(right.equals(""))
            return left;
      //  else
       // return x.op.equals(ExprBinary.Op.JOIN)? (x.right instanceof ExprCall  || x.right instanceof ExprBinary ? ("("+visitThis(x.left) +"."+visitThis(x.right)+")"): visitThis(x.left) +"."+visitThis(x.right) ):
                                              //  "("+visitThis(x.left) +" " +x.op.getLabel()+" "+visitThis(x.right)+")";

            return "("+visitThis(x.left) +" " +x.op.getLabel()+" "+visitThis(x.right)+")";
        //(x.right instanceof ExprCall ? ("("+visitThis(x.left) +"."+visitThis(x.right)+")"):visitThis(x.left) +"."+visitThis(x.right) )
    }

    @Override
    public String visit(ExprList x) throws Err {
        StringBuilder strtemp=new StringBuilder();
        String name =null;
        if (x.op.equals(ExprList.Op.AND)){
            name=" and ";
        }else if(x.op.equals(ExprList.Op.OR)){
            name=" or ";

        }else if (x.op.equals(ExprList.Op.DISJOINT)){
            name= "disjoint";

        }else if(x.op.equals(ExprList.Op.TOTALORDER)){
            name ="totalorder";

        }
        if(x.op.equals(ExprList.Op.AND) || x.op.equals(ExprList.Op.OR)){
            if(x.args.size()>0){
                if(x.op.equals(ExprList.Op.OR )&&x.args.size()>1 )
                    strtemp.append("(");

                strtemp.append(visitThis( x.args.get(0)));
                if(x.args.size()>1){
                    for (int i=1;i<x.args.size();i++){
                        strtemp.append(name +" \r\n        "+ visitThis(x.args.get(i)) );
                    }

                    if(x.op.equals(ExprList.Op.OR ))
                        strtemp.append(")");
                }
            }
        }
        return strtemp.toString();
    }

    @Override
    public String visit(ExprCall x) throws Err {
        StringBuilder temp=new StringBuilder();
        if(x.args.size()>0)
            temp.append("(");
        String name=x.fun.label;
        while(name.contains("/")){
            name=name.substring(name.indexOf("/")+1);
        }
        temp.append(name);
        if(x.args.size()>0){
            temp.append("[");
            for(Expr arg :x.args){
                temp.append(visitThis(arg)+",");
            }
            temp.deleteCharAt(temp.length()-1);
            temp.append("]");
            temp.append(")");
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
                return " " + x.string ;
        }
        return " " + x.num;
    }

    @Override
    public String visit(ExprITE x) throws Err {
        StringBuilder s=new StringBuilder();
        s.append(visitThis(x.cond)+" implies ");
        if(x.right!=null) {
            s.append(visitThis(x.left) + " else ");
            s.append(visitThis(x.right));
        }
        return s.toString();
    }

    @Override
    public String visit(ExprLet x) throws Err {
        StringBuilder s=new StringBuilder();
        s.append(" let "+ x.var.label+"=");
        s.append(visitThis(x.expr)+ " | ");
        s.append(visitThis(x.sub));
        return s.toString();
    }

    @Override
    public String visit(ExprQt x) throws Err {
        StringBuilder s= new StringBuilder();
        s.append("(");
        if(!x.op.equals(ExprQt.Op.COMPREHENSION)){
            s.append(x.op.getLabel() +" ");
        }else {
            s.append("{");
        }

        for (Decl decl :x.decls){
            if (decl.disjoint!=null)
                s.append(" disj ");

            for (Expr e: decl.names){
                s.append(visitThis(e)+",");
            }
            s.deleteCharAt(s.length() - 1);
            s.append(" :");
            s.append(visitThis(decl.expr)+",");
        }
        s.deleteCharAt(s.length()-1);


        s.append(" | ");
        s.append(visitThis(x.sub));

        if(x.op.equals(ExprQt.Op.COMPREHENSION)){
            s.append("}");
        }
        s.append(")");
        return s.toString();
    }

    @Override
    public String visit(ExprUnary x) throws Err {
        if(x.op.equals(ExprUnary.Op.NOOP)||x.op.equals(ExprUnary.Op.CAST2SIGINT)||x.op.equals(ExprUnary.Op.CAST2INT))
            return visitThis(x.sub);
        else if(x.op.equals(ExprUnary.Op.RCLOSURE)|| x.op.equals(ExprUnary.Op.CLOSURE)||x.op.equals(ExprUnary.Op.CARDINALITY))
            return x.op.getOpLabel() + "("+visitThis(x.sub)+")";
        else
            return x.op.getOpLabel().replaceAll(" of"," ") +" "+ visitThis(x.sub);

        //switch (x.op){
       //     case NOOP:
        //    case CAST2INT:
        //    case CAST2SIGINT:
         //       return visitThis(x.sub);
          //  default:  return x.op.getOpLabel().replaceAll(" of"," ") +" "+ visitThis(x.sub);
        //}
    }

    @Override
    public String visit(ExprVar x) throws Err {
        if(x.label.equals("this"))
            return "";
        else return x.label;
    }

    @Override
    public String visit(Sig x) throws Err {
        if (x.builtin){
            return x.label;
        }else
            return x.label.substring(5);
    }

    @Override
    public String visit(Sig.Field x) throws Err {
        return x.label;
    }
}
