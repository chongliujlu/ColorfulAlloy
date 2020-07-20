package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Err;

import java.util.HashMap;
import java.util.Map;

public class VisitOld2new extends VisitReturn<Expr> {
    public Map<Sig, Sig> getSigOld2new() {
        return sigOld2new;
    }

    public void setSigOld2new(Map<Sig, Sig> sigOld2new) {
        this.sigOld2new = sigOld2new;
    }

    Map<Sig,Sig> sigOld2new =new HashMap();
    Map<Sig.Field, Sig.Field> fieldOld2new=new HashMap();

    @Override
    public  Expr visit(ExprCall x) {
        return x;
    }

    @Override
    public Expr visit(ExprBinary x) throws Err {
        visitThis(x.left);
        visitThis(x.right);
        return x;
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        for(Expr e: x.args)
            visitThis(e);
        return x;
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        visitThis(x.cond);
        visitThis(x.left);
        visitThis(x.right);
        return x;
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        visitThis(x.expr);
        visitThis(x.sub);
        return x;
    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        return x;
    }

    @Override
    public Expr visit(ExprUnary x) throws Err {
        visitThis(x.sub);
        return x;
    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Sig x) throws Err {
        if (sigOld2new.containsKey(x)) {
            return sigOld2new.get(x);
        }
        return x;
    }

    @Override
    public Expr visit(Sig.Field x) throws Err {
        if (fieldOld2new.containsKey(x)) {
            return fieldOld2new.get(x);
        }
        return x;
    }
}
