package edu.mit.csail.sdg.ast;

public class VisiterRemoveFeatB extends VisitReturn<Expr> {
    public void setFeatB(Integer featB) {
        this.featB = featB;
    }

    Integer featB;
    @Override
    public  Expr visit(ExprCall x) {
        x.color.remove(featB);
        x.color.remove(-featB);

        return x;
    }

    @Override
    public Expr visit(ExprBinary x)  {
        x.color.remove(featB);
        x.color.remove(-featB);

        visitThis(x.left);
        visitThis(x.right);
        return x;
    }

    @Override
    public Expr visit(ExprList x)  {
        x.color.remove(featB);
        x.color.remove(-featB);
        for(Expr e: x.args)
            visitThis(e);
        return x;
    }

    @Override
    public Expr visit(ExprConstant x)  {
        x.color.remove(featB);
        x.color.remove(-featB);
        return x;
    }

    @Override
    public Expr visit(ExprITE x)  {
        x.color.remove(featB);
        x.color.remove(-featB);
        visitThis(x.cond);
        visitThis(x.left);
        visitThis(x.right);
        return x;
    }

    @Override
    public Expr visit(ExprLet x)  {
        x.color.remove(featB);
        x.color.remove(-featB);
        visitThis(x.expr);
        visitThis(x.sub);
        return x;
    }

    @Override
    public Expr visit(ExprQt x)  {
        x.color.remove(featB);
        x.color.remove(-featB);
        for(Decl d:x.decls){
            for(Expr n:d.names)
                visitThis(n);

            visitThis(d.expr);
        }
        visitThis(x.sub);
        return x;
    }

    @Override
    public Expr visit(ExprUnary x)  {
        x.color.remove(featB);
        x.color.remove(-featB);
        visitThis(x.sub);
        return x;
    }

    @Override
    public Expr visit(ExprVar x)  {
        x.color.remove(featB);
        x.color.remove(-featB);
        return x;
    }

    @Override
    public Expr visit(Sig x)  {
        return x;
    }

    @Override
    public Expr visit(Sig.Field x)  {
        return x;
    }
}