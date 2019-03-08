package edu.mit.csail.sdg.printExpr;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;

import java.util.HashSet;
import java.util.Set;

public  class ProjectFeatureExprVisitor extends VisitReturn<Expr> {
    Set<Integer> NFeatures=new HashSet<>();
    Set<Integer> PFeatures=new HashSet<>();

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
        if(markedWithNFeature())
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

        }else if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
        }
     return null;

    }

    /**
     * check if the Expr's negetive features is in selected features(for example, Expr :e is marked with NF1, selected : F1 and F2 )
     * @return
     */
    private boolean markedWithNFeature() {
        if(!NFeatures.isEmpty()){
            for(Integer i: NFeatures){
                if(MultiComboBox.selectedFeatures.contains(i)){
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
        if(markedWithNFeature())
            return null;

        if(PFeatures.isEmpty()){
            for(Expr expr: x.args){
                if(visitThis(expr)!=null){
                    temp.add(visitThis(expr));
                }
            }
            return ExprList.make(x.pos, x.closingBracket, x.op, temp.makeConst());

        }else if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(ExprCall x) throws Err {

        //need to change
        computeFeatures(x);
        if(markedWithNFeature())
            return null;

        if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        computeFeatures(x);
        if(markedWithNFeature())
            return null;

        if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        Expr cond=null; Expr leftExpr=null; Expr rightExpr=null;

        computeFeatures(x);
        if(markedWithNFeature())
            return null;

        if(PFeatures.isEmpty()){
            cond= visitThis(x.cond);
            leftExpr=  visitThis(x.left);
            rightExpr= visitThis(x.right);

            return ExprITE.make(x.pos,cond,leftExpr,rightExpr);

        }else if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
        }

        return null;
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        /*
            //change the type of expr,used in  Execute
            Type t=x.type;
            ConstList.TempList<Type.ProductType> entries =new ConstList.TempList<>();
//ConstList<ProductType> entries // PrimSig[]          types;
            //for each ProductType
           Iterator<Type.ProductType> iterator= t.iterator();
          while( iterator.hasNext()){
              Sig.PrimSig newPrimsigs[]=new Sig.PrimSig[iterator.next().arity()];

              for (int j=0; j<iterator.next().arity();j++){
                  if(sigOld2new.containsKey(iterator.next())&& sigOld2new.get(iterator.next())!=null){
                      newPrimsigs[j]=(Sig.PrimSig) sigOld2new.get(iterator.next());

                  }
                  else
                      newPrimsigs[j]=productTypes.get(j);
              }
          }

            Type newType=new Type(t.is_bool,entries.makeConst(),t.arities);

            x.type=newType;

*/
        computeFeatures(x);
        if(markedWithNFeature())
            return null;

        if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
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

            if(exp!=null){
                for(ExprHasName v:d.names){
                    Expr Exprout=visitThis(v);
                    declsnames.add((ExprVar) Exprout);
                }


                if(declsnames.size()!=0) {

                    Decl dd = new Decl(d.isPrivate, d.disjoint, d.disjoint2, declsnames.makeConst(), exp);
                    decls.add(dd);
                }
            }
        }
//project body
        Expr sub = visitThis(x.sub);


        if(sub!=null&& decls.size()!=0){
            return x.op.make(x.pos, x.closingBracket, decls.makeConst(), sub);
        }

        return null;
    }

    @Override
    public Expr visit(ExprUnary x) throws Err {
        Expr tempExpr=null;
        computeFeatures(x);
        if(markedWithNFeature())
            return null;
        if(PFeatures.isEmpty()){
            if(x.sub instanceof Sig || x.sub instanceof Sig.Field){
                return x;
            }else{
                tempExpr=  visitThis(x.sub);
                if(tempExpr!=null)
                    tempExpr=x.op.make(x.pos,tempExpr);
            }

        }else if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
        }
        return  tempExpr;

    }

    @Override
    public Expr visit(ExprVar x) throws Err {
/*
            //change Expr type
            Type t=x.type;
            ConstList.TempList<Type.ProductType> entries =new ConstList.TempList<>();
//ConstList<ProductType> entries // PrimSig[]          types;
            //每一个 ProductType
            for(Type.ProductType productTypes :t.getEntities()){
                Sig.PrimSig newPrimsigs[]=new Sig.PrimSig[productTypes.getTypes().length];
                for (int j=0; j< productTypes.getTypes().length;j++){
                    if(sigOld2new.containsKey(productTypes.get(j))&& sigOld2new.get(productTypes.get(j))!=null){
                        newPrimsigs[j]=(Sig.PrimSig) sigOld2new.get(productTypes.get(j));

                    }
                    else
                        newPrimsigs[j]=productTypes.get(j);
                }


                Type.ProductType p=new Type.ProductType(newPrimsigs);
                entries.add(p);

            }
            Type newType=new Type(t.is_bool,entries.makeConst(),t.arities);

            x.type=newType;

*/
        computeFeatures(x);
        if(markedWithNFeature())
            return null;

        if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x;
        }
        return null;
    }

    @Override
    public Expr visit(Sig x) throws Err {
        Sig signew=null;
        computeFeatures(x);
        if(markedWithNFeature())
            return null;
        if(PFeatures.isEmpty()||MultiComboBox.selectedFeatures.containsAll(PFeatures)){
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
            //ConstList.TempList<Sig.Field> tempList=new ConstList.TempList<>();

            for (Sig.Field f: x.getFields()){
                f.sig=signew;

                Expr exprout = visitThis(f);
                if (exprout!=null){

                    //修改指针
                    //   changePoint(exprout,x,xnew);

                    //help to find the old Field
                  //  List<Sig.Field> listold= signew.getFields().makeCopy();

                    signew.addField(f.label, exprout);
                  //  List<Sig.Field> list=signew.getFields().makeCopy();

                   // list.removeAll(listold);
                    // field2newField.put(f,list.get(0));
                }
            }
        }
        return signew;
    }
    @Override
    public Expr visit(Sig.Field x) throws Err {
        Expr tempExpr=null;
        computeFeatures(x);
        if(markedWithNFeature())
            return null;
        if(PFeatures.isEmpty()){

            tempExpr=  visitThis(x.decl().expr);
        }else if(MultiComboBox.selectedFeatures.containsAll(PFeatures)){
            return x.decl().expr;
        }

        return tempExpr;
    }

}
