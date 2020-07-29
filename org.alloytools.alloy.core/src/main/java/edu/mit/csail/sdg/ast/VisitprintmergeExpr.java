package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Err;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static edu.mit.csail.sdg.ast.ExprUnary.Op.LONEOF;
import static edu.mit.csail.sdg.ast.ExprUnary.Op.ONEOF;

public class VisitprintmergeExpr extends VisitReturn<String>{
    public void setParentFeats(Set<Integer> parentFeats) {
        this.parentFeats = parentFeats;
    }

    public Set<Integer> parentFeats=new HashSet<>();
    @Override
    public  String visit(ExprCall x) {
        StringBuilder print=new StringBuilder();
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        parentFeats=x.color.keySet();


        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        print.append(coloF);
        String name= x.fun.label;
        while (name.contains("/")){
            name=name.substring(name.indexOf("/")+1);
        }
        print.append("("+name);
        // tempExpr.append(x.fun.label.substring(x.fun.label.indexOf("/")+1));
        if(x.args.size()>0) {
            print.append("[");
            for (Expr arg : x.args) {
                parentFeats=x.color.keySet();
                print.append(visitThis(arg) + ",");
            }

            print.deleteCharAt(print.length() - 1);
            print.append("]");
        }
        print.append(")");
        print.append(colorB);
        return print.toString();
    }

    @Override
    public String visit(ExprBinary x) throws Err {
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        parentFeats=x.color.keySet();

        StringBuilder print=new StringBuilder();
        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        if(x.op==ExprBinary.Op.PLUS||x.op==ExprBinary.Op.INTERSECT)
            print.append("(");

        print.append(coloF+visitThis(x.left));
        print.append(x.op==ExprBinary.Op.JOIN? x.op :" "+x.op+" ");

        parentFeats=x.color.keySet();
        print.append(x.op.equals(ExprBinary.Op.JOIN) && x.right instanceof ExprBinary &&
                ((ExprBinary)x.right).op.equals(ExprBinary.Op.JOIN)? "("+visitThis(x.right)+")"+
                    colorB:visitThis(x.right)+colorB);

        if(x.op==ExprBinary.Op.PLUS||x.op==ExprBinary.Op.INTERSECT)
            print.append(")");
        return print.toString();
    }

    @Override
    public String visit(ExprList x) throws Err {
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);


        StringBuilder print=new StringBuilder();
        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        print.append(coloF);
        String name=x.op.name();
        if(name.equals("AND")) name=" and ";
        if(name.equals("OR")) name=" or ";

        for(Expr e: x.args){
            parentFeats=x.color.keySet();
            print.append(visitThis(e)+" ");
            print.append(x.op.name().equals(ExprBinary.Op.AND)?name:" "+name);
        }

        print.deleteCharAt(print.length()-1);
        print.deleteCharAt(print.length()-1);
        print.deleteCharAt(print.length()-1);
        if(x.op.equals(ExprList.Op.AND))
            print.deleteCharAt(print.length()-1);
        print.append(colorB);
        return print.toString();
    }

    @Override
    public String visit(ExprConstant x) throws Err {
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        parentFeats=x.color.keySet();

        StringBuilder print=new StringBuilder();
        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        print.append(coloF);

        if(x.op.equals(ExprConstant.Op.TRUE))
            print.append( " true ");
        if(x.op.equals(ExprConstant.Op.FALSE))
            print.append( " false ");
        if(x.op.equals(ExprConstant.Op.IDEN))
            print.append(" iden ");

        if(x.op.equals(ExprConstant.Op.MAX))
            print.append(" fun/max ");
        if(x.op.equals(ExprConstant.Op.MIN))
            print.append(" fun/min ");
        if(x.op.equals(ExprConstant.Op.NEXT))
            print.append( " fun/next ");
        if(x.op.equals(ExprConstant.Op.EMPTYNESS))
            print.append( " none ");
        if(x.op.equals(ExprConstant.Op.STRING))
            print.append( " " + x.string+" ");
        if(x.op.equals(ExprConstant.Op.NUMBER))
            print.append( " " + x.num+" ");
        print.append(colorB);
        return print.toString();
    }

    @Override
    public String visit(ExprITE x) throws Err {
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        parentFeats=x.color.keySet();

        StringBuilder print=new StringBuilder();
        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        print.append(coloF);

        print.append( visitThis(x.cond));
        print.append(visitThis(x.left));
        print.append(visitThis(x.right));

        print.append(colorB);
        return print.toString();
    }

    @Override
    public String visit(ExprLet x) throws Err {
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        parentFeats=x.color.keySet();

        StringBuilder print=new StringBuilder();
        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        print.append(coloF);

        print.append(visitThis(x.expr));
        print.append(visitThis(x.sub));

        print.append(colorB);
        return print.toString();
    }

    @Override
    public String visit(ExprQt x) throws Err {
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        parentFeats=x.color.keySet();

        StringBuilder print=new StringBuilder();
        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        print.append(coloF);
        if(!x.op.equals(ExprQt.Op.COMPREHENSION))
            //all，no
            print.append(x.op.getLabel() +" ");

        for (Decl decl :x.decls){
            if(decl.disjoint!=null)
                print.append( " disj "); //"disj" key word
            for (Expr e: decl.names){
                parentFeats=x.color.keySet();
                print.append(visitThis(e)+",");
            }
            print.deleteCharAt(print.length() - 1);
            print.append(": ");

            //  for(Integer i:x.color.keySet()){
            //     decl.expr.color.remove(i);
            //  }
            parentFeats=x.color.keySet();
            print.append(visitThis(decl.expr)+",");
        }

        print.deleteCharAt(print.length()-1);
        print.append(" | ");
        // x.sub.color.remove(x.color.keySet());
        parentFeats=x.color.keySet();
        print.append(visitThis(x.sub));
        print.append(colorB);
        return print.toString();
    }

    @Override
    public String visit(ExprUnary x) throws Err {
        Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        parentFeats=x.color.keySet();

        StringBuilder print=new StringBuilder();
        StringBuilder coloF=new StringBuilder();
        StringBuilder colorB=new StringBuilder();
        if(xcolor.size()>0)
            x.printcolor(coloF,colorB,xcolor);

        print.append(coloF);

        if(x.op.equals(ExprUnary.Op.SETOF))
            print.append(" set ");
        else if(x.op.equals(ExprUnary.Op.SOMEOF))
            print.append(" some ");
        else if(x.op.equals(LONEOF))
            print.append(" lone ");
        else if(x.op.equals(ONEOF))
            print.append(" one ");
        else if(x.op.equals(ExprUnary.Op.EXACTLYOF))
            print.append(" exactly ");
        else if(x.op.equals(ExprUnary.Op.RCLOSURE)||x.op.equals(ExprUnary.Op.CLOSURE)||
                x.op.equals(ExprUnary.Op.CARDINALITY))
            print.append(" "+x.op.getOpLabel()+"("); // (

        else if(x.op.equals(ExprUnary.Op.NOT)||x.op.equals(ExprUnary.Op.NO)||
                x.op.equals(ExprUnary.Op.SOME)||x.op.equals(ExprUnary.Op.ONE)||
                x.op.equals(ExprUnary.Op.LONE)||x.op.equals(ExprUnary.Op.TRANSPOSE))
            print.append(" "+x.op.getOpLabel()+" ");
        print.append(visitThis(x.sub));


        if(x.op.equals(ExprUnary.Op.RCLOSURE)||x.op.equals(ExprUnary.Op.CLOSURE)||
                x.op.equals(ExprUnary.Op.CARDINALITY))
            print.append(")");  // )
        print.append(colorB);
        return print.toString();
    }

    @Override
    public String visit(ExprVar x) throws Err {
        //  Set <Integer> xcolor=sub(x.color.keySet(),parentFeats);
        //  parentFeats=x.color.keySet();

        StringBuilder print=new StringBuilder();
        //   StringBuilder coloF=new StringBuilder();
        //   StringBuilder colorB=new StringBuilder();
        //  if(xcolor.size()>0)
        //      printcolor(coloF,colorB,xcolor);

        //  print.append(coloF);
        print.append(" "+x.label+ " ");
        return print.toString();
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
        return x.label;
    }

    /**
     * return sub set (a-b)
     * @param a
     * @param b
     * @return
     */
    private HashSet<Integer> sub(Set<Integer> a, Set<Integer> b) {
        List<Integer> result = new ArrayList<>();
        if(a!=null){
            result = new ArrayList<>(a);
            result.removeAll(b);
        }
        return new HashSet<>(result);
    }

}
