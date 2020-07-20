package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class VisitRefactor extends VisitReturn<Expr> {
    static Set<Integer> featB=new HashSet<>();
    @Override
    public  Expr visit(ExprCall x) {
        return x;
    }

    @Override
    public Expr visit(ExprBinary x) throws Err {
        Expr left=visitThis(x.left);
        Expr right=visitThis(x.right);

        if(x.op.equals(ExprBinary.Op.INTERSECT)){
            //featB=new HashSet<>();
            if(left instanceof ExprBinary && ((ExprBinary) left).op==ExprBinary.Op.JOIN &&
                    right instanceof ExprBinary && ((ExprBinary) right).op==ExprBinary.Op.JOIN &&
                    ((ExprBinary) left).left.toString().equals(((ExprBinary) right).left.toString())&&
                    left.compareMergeLaw(right)!=null){

                VisiterRemoveFeatB visiterRemoveFeatB=new VisiterRemoveFeatB();
                ((ExprBinary) left).left.accept(visiterRemoveFeatB);
                Expr er= ExprBinary.Op.INTERSECT.make(((ExprBinary) left).left.pos,
                        ((ExprBinary) left).left.closingBracket,((ExprBinary) left).right,((ExprBinary) right).right,((ExprBinary) left).left.color);

                return  ExprBinary.Op.JOIN.make(((ExprBinary) left).left.pos,((ExprBinary) left).left.closingBracket,
                        ((ExprBinary) left).left,er,((ExprBinary) left).left.color);

            }else if(left instanceof ExprBinary && ((ExprBinary) left).op==ExprBinary.Op.JOIN &&
                    right instanceof ExprBinary && ((ExprBinary) right).op==ExprBinary.Op.JOIN &&
                    ((ExprBinary) left).right.toString().equals(((ExprBinary) right).right.toString())&&
                    left.compareMergeLaw(right)!=null){

                VisiterRemoveFeatB visiterRemoveFeatB=new VisiterRemoveFeatB();
                ((ExprBinary) left).right.accept(visiterRemoveFeatB);
                Expr er= ExprBinary.Op.INTERSECT.make(((ExprBinary) x.left).right.pos,
                        ((ExprBinary) left).right.closingBracket,((ExprBinary) left).left,
                        ((ExprBinary) right).left,((ExprBinary) left).right.color);

                return  ExprBinary.Op.JOIN.make(((ExprBinary) left).right.pos,((ExprBinary) left).right.closingBracket,
                        er,((ExprBinary) left).right,((ExprBinary) left).right.color);
            }
        }else if(x.op.equals(ExprBinary.Op.AND)) {
            if (left instanceof ExprBinary && ((ExprBinary) left).op == ExprBinary.Op.JOIN &&
                    right instanceof ExprBinary && ((ExprBinary) right).op == ExprBinary.Op.JOIN &&
                    ((ExprBinary) left).left.toString().equals(((ExprBinary) right).left.toString())){
                VisiterRemoveFeatB visiterRemoveFeatB = new VisiterRemoveFeatB();
                ((ExprBinary) left).left.accept(visiterRemoveFeatB);
                Expr er = ExprBinary.Op.AND.make(((ExprBinary) left).left.pos,
                        ((ExprBinary) left).left.closingBracket, ((ExprBinary) left).right,
                        ((ExprBinary) right).right, ((ExprBinary) left).left.color);

                return ExprBinary.Op.JOIN.make(((ExprBinary) left).left.pos, ((ExprBinary) left).left.closingBracket,
                        ((ExprBinary) left).left, visitThis(er), ((ExprBinary) left).left.color);
            }else if (left instanceof ExprBinary && ((ExprBinary) left).op == ExprBinary.Op.JOIN &&
                    right instanceof ExprBinary && ((ExprBinary) right).op == ExprBinary.Op.JOIN &&
                    ((ExprBinary) left).right.toString().equals(((ExprBinary) right).right.toString())) {
                VisiterRemoveFeatB visiterRemoveFeatB = new VisiterRemoveFeatB();
                ((ExprBinary) left).right.accept(visiterRemoveFeatB);
                Expr er = ExprBinary.Op.AND.make(((ExprBinary) left).right.pos,
                        ((ExprBinary) left).right.closingBracket, ((ExprBinary) left).left, ((ExprBinary) right).left, ((ExprBinary) left).right.color);

                return ExprBinary.Op.JOIN.make(((ExprBinary) left).right.pos, ((ExprBinary) left).right.closingBracket,
                        visitThis(er), ((ExprBinary) left).right, ((ExprBinary) left).right.color);
            }
        }else if(x.op.equals(ExprBinary.Op.PLUS)){

           // featB=new HashSet<>();
            if(left.toString().equals(right.toString()) ){
                VisiterRemoveFeatB visiterRemoveFeatB=new VisiterRemoveFeatB();
                if(left.color.keySet().equals(right.color.keySet())){
                    return  left;
                } else if( left.compareMergeLaw(right)!=null){
                   return left.accept(visiterRemoveFeatB);
                }

            }

        }

        return x.op.make(x.pos, x.closingBracket,  left, right, x.color);
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        ConstList.TempList<Expr> temp = new ConstList.TempList<Expr>(x.args.size());
        if(x.op.equals(ExprList.Op.AND)||x.op.equals(ExprList.Op.OR)){
            temp.addAll(x.args);

            Set<Expr> visit;
            //equal
            boolean notfinish= true;
            while(notfinish){
                notfinish= mergeExprEqual(temp);
            }
            notfinish=true;

            while(notfinish){
                boolean changed=false;
                visit=new HashSet<>();
                ConstList.TempList<Expr>  temp2 =temp.clone();
                for(Expr e: temp2.makeConst()){
                    if(visit.contains(e)) continue;
                    visit.add(e);
                    if(e instanceof ExprQt){
                        for(Expr e2:temp2.makeConst()){
                            if(visit.contains(e2)) continue;
                            if(e2 instanceof ExprQt){
                               // featB=new HashSet<>();
                                if(e.compareMergeLaw(e2)!=null){
                                    if(((ExprQt) e).decls.size()== (((ExprQt) e2).decls.size())){
                                        boolean match=true;
                                        for(Decl d1i:((ExprQt) e).decls){
                                            boolean find=false;
                                            for(Decl d2j:((ExprQt) e2).decls){
                                                if(d1i.names.toString().equals(d2j.names.toString())){
                                                    find=true;
                                                    break;
                                                }
                                            }
                                            if(!find) {
                                                match=false;
                                                break;}
                                        }

                                        //进行merge
                                        if(match){
                                            temp.remove(temp.indexOf(e));
                                            temp.remove(temp.indexOf(e2));
                                            visit.add(e2);

                                            Map cl=new HashMap(e.color);
                                            for(Integer i:featB){
                                                cl.remove(i);
                                                cl.remove(-i);
                                            }
                                            ConstList.TempList<Decl> decls = new ConstList.TempList<Decl>(((ExprQt) e).decls.size());
                                            //merge Decl
                                            for(Decl d1i:((ExprQt) e).decls){
                                                for(Decl d2j:((ExprQt) e2).decls){
                                                    if(d1i.names.toString().equals(d2j.names.toString())){
                                                        ConstList.TempList<ExprVar> n = new ConstList.TempList<ExprVar>(d1i.names.size());
                                                        for (ExprHasName v : d1i.names)
                                                            n.add(ExprVar.make(v.pos, v.label, cl));
                                                        Expr exp=null;
                                                        if(d1i.expr instanceof ExprUnary && d2j.expr instanceof ExprUnary){
                                                            Expr expnew=ExprBinary.Op.PLUS.make(d1i.span(),d1i.expr.closingBracket,((ExprUnary) d1i.expr).sub,((ExprUnary) d2j.expr).sub,cl);
                                                            exp=((ExprUnary) d1i.expr).op.make(expnew.pos,expnew,cl);
                                                        }else{
                                                            exp=ExprBinary.Op.PLUS.make(d1i.span(),d1i.expr.closingBracket, d1i.expr,d2j.expr,cl);
                                                        }

                                                        Decl dd = new Decl(d1i.isPrivate, d1i.disjoint,d1i.disjoint2, n.makeConst(), visitThis(exp),cl);
                                                        decls.add(dd);
                                                        break;
                                                    }
                                                }
                                            }
                                            //mergr sub
                                            Expr sub=ExprBinary.Op.AND.make(e.pos,e.closingBracket,visitThis(((ExprQt) e).sub),visitThis(((ExprQt) e2).sub),cl);
                                            e=((ExprQt) e).op.make(x.pos, x.closingBracket, decls.makeConst(), sub, cl);
                                            changed=true;
                                        }
                                    }
                                }
                            }
                        }
                    }else if(e instanceof ExprBinary && ((ExprBinary) e).op.equals(ExprBinary.Op.IN) ){
                        for(Expr e2:temp2.makeConst()){
                            if(visit.contains(e2)) continue;
                            if(e2 instanceof ExprBinary && ((ExprBinary) e).op.equals(ExprBinary.Op.IN)){
                                if(e.compareMergeLaw(e2)!=null){
                                    temp.remove(temp.indexOf(e));
                                    temp.remove(temp.indexOf(e2));
                                    changed=true;
                                    if(((ExprBinary) e).left.toString().equals(((ExprBinary) e2).left.toString())){
                                        visit.add(e2);
                                        VisiterRemoveFeatB visiterRemoveFeatB=new VisiterRemoveFeatB();
                                        ((ExprBinary) e).left.accept(visiterRemoveFeatB);
                                        Expr eNew=ExprBinary.Op.INTERSECT.make(e.pos,e.closingBracket,visitThis(((ExprBinary) e).right),visitThis(((ExprBinary) e2).right),((ExprBinary) e).left.color);
                                        e=ExprBinary.Op.IN.make(e.pos,e.closingBracket,((ExprBinary) e).left,eNew,((ExprBinary) e).left.color);
                                    }
                                }
                            }
                        }
                    }
                    if(temp.contains(e))
                        temp.remove(temp.indexOf(e));
                    temp.add(visitThis(e));
                }
                if(!changed)
                    notfinish=false;
            }

        }else {
            temp = new ConstList.TempList<Expr>(x.args.size());
            for(Expr e:x.args)
                temp.add(visitThis(e));
        }



        return ExprList.make(x.pos, x.closingBracket, x.op, temp.makeConst(), x.color);

    }

    private boolean mergeExprEqual(ConstList.TempList<Expr> temp) {
        boolean changed=false;
        Set<Expr> visit=new HashSet<>();
        for(Expr e: temp.clone().makeConst()){
            if(visit.contains(e)) continue;
            visit.add(e);
            for(Expr e2:temp.clone().makeConst()){
                if(visit.contains(e2)) continue;

               // featB=new HashSet<>();
                if(e.toString().equals(e2.toString()) && e.compareMergeLaw(e2)!=null){
                    temp.remove(temp.indexOf(e));
                    temp.remove(temp.indexOf(e2));
                    changed=true;
                    VisiterRemoveFeatB visiterRemoveFeatB=new VisiterRemoveFeatB();
                    e.accept(visiterRemoveFeatB);

                    visit.add(e2);
                    break;
                }
            }
            if(!temp.contains(e))
                temp.add(e);
        }
        if(changed)
            return true;
        return false;
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        return ExprITE.make(x.pos, visitThis(x.cond), visitThis(x.left),  visitThis(x.right), x.color);
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        return ExprLet.make(x.pos, x.var, visitThis(x.expr), visitThis(x.sub), x.color); // [HASLab] colorful Alloy

    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        ConstList.TempList<Decl> decls = new ConstList.TempList<Decl>(x.decls.size());
        for (Decl d : x.decls) {
            Decl dd = new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.names, visitThis(d.expr), d.color); // [HASLab] colorful Alloy
            decls.add(dd);
        }

        return x.op.make(x.pos, x.closingBracket, decls.makeConst(), visitThis(x.sub), x.color); // [HASLab] colorful Alloy
    }

    @Override
    public Expr visit(ExprUnary x) throws Err {
        return x.op.make(x.pos,visitThis(x.sub),x.color);

    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Sig x) throws Err {


        return x;
    }

    @Override
    public Expr visit(Sig.Field x) throws Err {
        return x;
    }

    private  class VisiterRemoveFeatB extends VisitReturn<Expr> {

        @Override
        public  Expr visit(ExprCall x) {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            return x;
        }

        @Override
        public Expr visit(ExprBinary x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            visitThis(x.left);
            visitThis(x.right);
            return x;
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            for(Expr e: x.args)
                visitThis(e);
            return x;
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            return x;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            visitThis(x.cond);
            visitThis(x.left);
            visitThis(x.right);
            return x;
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            visitThis(x.expr);
            visitThis(x.sub);
            return x;
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            for(Decl d:x.decls){
                for(Expr n:d.names)
                    visitThis(n);

                visitThis(d.expr);
            }
            visitThis(x.sub);
            return x;
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            visitThis(x.sub);
            return x;
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            for(Integer b: featB){
                x.color.remove(b);
                x.color.remove(-b);
            }
            return x;
        }

        @Override
        public Expr visit(Sig x) throws Err {
            return x;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            return x;
        }

    }

}
