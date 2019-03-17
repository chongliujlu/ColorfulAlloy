package edu.mit.csail.sdg.printExpr;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;

import java.util.HashSet;
import java.util.Set;

public  class expressionProject extends VisitReturn<Expr> {
    Set<Integer> NFeatures=new HashSet<>();
    Set<Integer> PFeatures=new HashSet<>();


    public static Set<Integer> runfeatures; //colorful Alloy

    /**
     * computer the Negative Features and positive Features respectively
     * @param x
     */
    public void computeFeatures(Expr x){
        NFeatures.clear();
        PFeatures.clear();
        for(Integer i: x.color){
            if(i<0)
                NFeatures.add(-i);
            else PFeatures.add(i);
        }
    }

    @Override
    public Expr visit(ExprBinary x) throws Err {
        Expr leftExpr=null;
        Expr rightExpr=null;
        //not marked with neg feature
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;

        if(PFeatures.isEmpty()){
            leftExpr=  visitThis(x.left);
            rightExpr= visitThis(x.right);

            if (leftExpr==null)
                return rightExpr;
            else if (rightExpr==null)
                return leftExpr;
            else
                return  x.op.make(x.pos, x.closingBracket, leftExpr, rightExpr);

        }else if(runfeatures.containsAll(PFeatures)){
            return x;
        }
        return null;

    }

    /**
     * check if the Expr's negetive features is in selected features(for example, Expr :e is marked with NF1, selected : F1 and F2 )
     * @return
     */
    private boolean markedWithNFeature(Set<Integer> color) {
        if(!color.isEmpty()){
            for(Integer i: color){
                if(runfeatures.contains(-i)){
                    return true;
                }

            }
        }
        return false;
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        ConstList.TempList<Expr> temp = new ConstList.TempList<>(x.args.size());

        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;

        if(PFeatures.isEmpty()){
            for(Expr expr: x.args){
                if(visitThis(expr)!=null){
                    temp.add(visitThis(expr));
                }
            }
            return ExprList.make(x.pos, x.closingBracket, x.op, temp.makeConst());

        }else if(runfeatures.containsAll(PFeatures)){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(ExprCall x) throws Err {
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;
        if(runfeatures.containsAll(PFeatures)){
            return x;
        }else if(runfeatCointainNoPFeature(runfeatures))
            return x;
        return null;
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;

        if(runfeatures.containsAll(PFeatures)){
            return x;
        }else if(runfeatCointainNoPFeature(runfeatures))
            return x;
        return null;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        Expr cond=null; Expr leftExpr=null; Expr rightExpr=null;

        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;

        if(PFeatures.isEmpty()){
            cond= visitThis(x.cond);
            leftExpr=  visitThis(x.left);
            rightExpr= visitThis(x.right);

            return ExprITE.make(x.pos,cond,leftExpr,rightExpr);

        }else if(runfeatures.containsAll(PFeatures)){
            return x;
        }else if(runfeatCointainNoPFeature(runfeatures))
            return x;

        return null;
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;
        // no positive feature marked
        if(PFeatures.isEmpty())
            return ExprLet.make(x.pos,x.var,visitThis(x.expr),visitThis(x.sub));
        if(runfeatures.containsAll(PFeatures)){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;


        if(PFeatures.isEmpty()||runfeatures.containsAll(PFeatures)||runfeatCointainNoPFeature(runfeatures) ) {

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
        }
        return null;
    }

    @Override
    public Expr visit(ExprUnary x) throws Err {
        Expr tempExpr=null;
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;
        if(PFeatures.isEmpty()){
            if(x.sub instanceof Sig || x.sub instanceof Sig.Field){
                return x;
            }else{
                tempExpr=  visitThis(x.sub);
                if(tempExpr!=null)
                    tempExpr=x.op.make(x.pos,tempExpr);
            }

        }else if(runfeatures.containsAll(PFeatures)){
            return x;
        }else if(runfeatCointainNoPFeature(runfeatures))
            return x;
        return  tempExpr;

    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;
        else if(runfeatures.containsAll(PFeatures)||runfeatCointainNoPFeature(runfeatures)){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(Sig x) throws Err {
        Sig signew=null;
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;
        if(PFeatures.isEmpty()||runfeatures.containsAll(PFeatures) ||runfeatCointainNoPFeature(runfeatures)){
            //used to generate new Sig
            Attr []attributes = new Attr[x.attributes.size()];
            for( int i=0; i<x.attributes.size();i++){
                attributes[i]=x.attributes.get(i);
            }

            if(x instanceof Sig.PrimSig)
                signew=new Sig.PrimSig(x.label,((Sig.PrimSig) x).parent,attributes);
            else if (x instanceof Sig.SubsetSig)
                signew=new Sig.SubsetSig(x.label,((Sig.SubsetSig) x).parents,attributes);

            signew.attributes=x.attributes;

            for (Sig.Field f: x.getFields()){
                f.sig=signew;

                Expr exprout = visitThis(f);
                if (exprout!=null){

                    signew.addField(f.label, exprout);
                }
            }
        }

        return signew;
    }
    @Override
    public Expr visit(Sig.Field x) throws Err {
        Expr tempExpr=null;
        computeFeatures(x);
        if(markedWithNFeature(x.color))
            return null;
        if(PFeatures.isEmpty()){

            tempExpr=  visitThis(x.decl().expr);
        }else if(runfeatures.containsAll(PFeatures)||runfeatCointainNoPFeature(runfeatures)){
            return x.decl().expr;
        }

        return tempExpr;
    }

    /**
     * used when selected ➊  feature but marked with  ➁  ,return Expr
     *                    ➊ ➂                         ➁ , return null
     * @param runfeatures
     * @return
     */
    private boolean runfeatCointainNoPFeature(Set<Integer> runfeatures) {
        boolean notContains=true;
        if(!runfeatures.isEmpty())
            for(Integer i: runfeatures){
                if(i<0)
                continue;
                else
                {
                    notContains=false;
                    break;
                }

            }
        return notContains;
    }
}
