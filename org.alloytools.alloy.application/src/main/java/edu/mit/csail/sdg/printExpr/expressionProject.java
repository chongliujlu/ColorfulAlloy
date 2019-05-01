package edu.mit.csail.sdg.printExpr;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;
import java.util.HashSet;
import java.util.Set;

public  class expressionProject extends VisitReturn<Expr> {
    /**
     * store marked Negative features for Expr, for example,
     * if a expression painted with ➊➋, NFeature={1,2}
     */
    Set<Integer> NFeatures=new HashSet<>();
    /**
     * store marked Negative features for Expr, for example,
     * if a expression painted with ➀➁, PFeature={1,2}
     */
    Set<Integer> PFeatures=new HashSet<>();

    /**
     * features in the execute command, for example,
     * run {} with exactly ➀,➋ for 3 , executefeats={1,-2}
     */
    public static Set<Integer> executefeats; //colorful Alloy

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

        if(paintWithOppositeFeature(x.color))
            return null;

        computeFeatures(x);

        // executefeats: null,PFeatures:null; executefeats:PF1... PFeatures: null; executefeats:PF1, NF2 ,PF3... PFeatures: PF3,NF4
        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature()){

            Expr leftExpr=  visitThis(x.left);
           Expr rightExpr= visitThis(x.right);

            if (leftExpr==null)
                return rightExpr;
            else if (rightExpr==null)
                return leftExpr;
            else
                return  x.op.make(x.pos, x.closingBracket, leftExpr, rightExpr);

        }
        return null;

    }

    /**
     * check if the opposite feature is painted
     * (for example, Expr :e is marked with NF1, selected : F1 and F2 ;
     *                                      F1, selected: NF1                             )
     * @return
     */
    private boolean paintWithOppositeFeature(Set<Integer> color) {
        if(!color.isEmpty()){
            for(Integer i: color){
                if(executefeats.contains(-i)){
                    return true;
                }

            }
        }
        return false;
    }

    @Override
    public Expr visit(ExprList x) throws Err {

        if(paintWithOppositeFeature(x.color))
            return null;

        ConstList.TempList<Expr> temp = new ConstList.TempList<>(x.args.size());
        computeFeatures(x);

        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature()){
            for(Expr expr: x.args){
                if(visitThis(expr)!=null){
                    temp.add(visitThis(expr));
                }
            }
            return ExprList.make(x.pos, x.closingBracket, x.op, temp.makeConst());

        }
        return null;
    }

    @Override
    public Expr visit(ExprCall x) throws Err {

        if(paintWithOppositeFeature(x.color))
            return null;
        computeFeatures(x);
        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature()){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        if(paintWithOppositeFeature(x.color))
            return null;

        computeFeatures(x);

        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature()){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {

        if(paintWithOppositeFeature(x.color))
            return null;
        Expr cond=null; Expr leftExpr=null; Expr rightExpr=null;

        computeFeatures(x);

        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature() ){
            cond= visitThis(x.cond);
            leftExpr=  visitThis(x.left);
            rightExpr= visitThis(x.right);

            return ExprITE.make(x.pos,cond,leftExpr,rightExpr);

        }

        return null;
    }

    @Override
    public Expr visit(ExprLet x) throws Err {

        if(paintWithOppositeFeature(x.color))
            return null;
        computeFeatures(x);
        // no positive feature marked
        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature() )
            return ExprLet.make(x.pos,x.var,visitThis(x.expr),visitThis(x.sub));

        return null;
    }

    @Override
    public Expr visit(ExprQt x) throws Err {

        if(paintWithOppositeFeature(x.color))
            return null;

        computeFeatures(x);
        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature() ) {

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
        if(paintWithOppositeFeature(x.color))
            return null;

        Expr tempExpr=null;
        computeFeatures(x);
        //1,2   1,0                           -1   , 2,3,4
        if(executefeats.containsAll(PFeatures)|| runfeatCointainOnlyNFeature()){
            if(x.sub instanceof Sig || x.sub instanceof Sig.Field){
                return x;
            }else{
                tempExpr=  visitThis(x.sub);
                if(tempExpr!=null)
                    tempExpr=x.op.make(x.pos,tempExpr);

            }

        }
//
        return  tempExpr;
        //return x;

    }

    @Override
    public Expr visit(ExprVar x) throws Err {

        if(paintWithOppositeFeature(x.color))
            return null;
        computeFeatures(x);
        if(executefeats.containsAll(PFeatures)||runfeatCointainOnlyNFeature()){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(Sig x) throws Err {
        if(paintWithOppositeFeature(x.color))
            return null;

        Sig signew=null;
        computeFeatures(x);

        if(executefeats.containsAll(PFeatures) ||(runfeatCointainOnlyNFeature())){
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
        if(paintWithOppositeFeature(x.color))
            return null;

        Expr tempExpr=null;
        computeFeatures(x);

        if(executefeats.containsAll(PFeatures)||runfeatCointainOnlyNFeature()){
//???
            tempExpr=  visitThis(x.decl().expr);
        }

        return tempExpr;
    }

    /**
     * used when selected ➊  feature but marked with  ➁  ,return Expr
     *
     *                    ➊ ➂                         ➁ , return null
     * @param
     * @return
     */
    private boolean runfeatCointainOnlyNFeature() {
        if(!executefeats.isEmpty())
            for(Integer i: executefeats){
                if(i<0)
                return true;

            }
        return false;
    }
}
