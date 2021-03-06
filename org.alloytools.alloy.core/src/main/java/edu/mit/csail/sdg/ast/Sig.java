/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.ast;

import static edu.mit.csail.sdg.alloy4.TableView.clean;
import static edu.mit.csail.sdg.ast.ExprUnary.Op.*;
import static edu.mit.csail.sdg.ast.ExprUnary.Op.SOMEOF;

import java.util.*;

import edu.mit.csail.sdg.parser.CompModule;
import org.alloytools.util.table.Table;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.TableView;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.ast.Attr.AttrType;

/** Mutable; represents a signature. */

public abstract class Sig extends Expr implements Clause {

    /** The built-in "univ" signature. */
    public static final PrimSig UNIV   = new PrimSig("univ", null, false);

    /** The built-in "Int" signature. */
    public static final PrimSig SIGINT = new PrimSig("Int", UNIV, false);

    /** The built-in "seq/Int" signature. */
    public static final PrimSig SEQIDX = new PrimSig("seq/Int", SIGINT, true);

    /** The built-in "String" signature. */
    public static final PrimSig STRING = new PrimSig("String", UNIV, true);

    /** The built-in "none" signature. */
    public static final PrimSig NONE   = new PrimSig("none", null, false);

    /** The built-in "none" signature. */
    public static final PrimSig GHOST  = mkGhostSig();

    private static final PrimSig mkGhostSig() {
        try {
            return new PrimSig("Univ", (PrimSig) null, new Attr[0]);
        } catch (Err e) {
            return null; // never happens
        }
    }

    /**
     * Returns the name for this sig; this name need not be unique.
     */
    @Override
    public final String toString() {
        return label;
    }
    public final String print() {
        return label;
    }

    /** {@inheritDoc} */
    @Override
    public final void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(label);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("sig ").append(label).append(" with type=").append(type).append('\n');
        }
    }
    public final void print(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(label.contains("/")?label.substring(label.indexOf("/")+1):label);
        } else {
        }
    }


    /** {@inheritDoc} */
    @Override
    public final Pos span() {
        return pos;
    }

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warns) {
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /**
     * Store the list of attributes.
     */
    // [HASLab] colorful Alloy, removed final
    public ConstList<Attr>       attributes;

    /**
     * True if this sig is one of the built-in sig.
     * <p>
     * Note: if builtin==true, then we ensure it is not abstract
     */
    public final boolean         builtin;

    /**
     * Nonnull if this sig is abstract.
     * <p>
     * Note: if a sig is abstract, then it cannot and will not be a subset sig.
     */
    public final Pos             isAbstract;

    /**
     * Nonnull if this sig is a PrimSig and therefore not a SubsetSig.
     */
    public final Pos             isSubsig;

    /**
     * Nonnull if this sig is a SubsetSig and therefore not a PrimSig.
     * <p>
     * Note: if a sig is a subset sig, then it cannot and will not be abstract.
     */
    public final Pos             isSubset;

    /**
     * Nonnull if this sig's multiplicity is declared to be lone.
     * <p>
     * Note: at most one of "lone", "one", "some" can be nonnull for each sig.
     */
    public final Pos             isLone;

    /**
     * Nonnull if this sig's multiplicity is declared to be one.
     * <p>
     * Note: at most one of "lone", "one", "some" can be nonnull for each sig.
     */
    public final Pos             isOne;

    /**
     * Nonnull if this sig's multiplicity is declared to be some.
     * <p>
     * Note: at most one of "lone", "one", "some" can be nonnull for each sig.
     */
    public  final Pos             isSome;

    /**
     * Nonnull if the user wanted this sig to be private.
     * <p>
     * Note: this value is always null for builtin sigs.
     */
    public final Pos             isPrivate;

    /**
     * Nonnull if the sig is toplevel and is an enum.
     * <p>
     * Note: this value is always null for builtin sigs.
     */
    public final Pos             isEnum;

    /**
     * Nonnull if this sig is a meta sig.
     * <p>
     * Note: this value is always null for builtin sigs.
     */
    public final Pos             isMeta;

    /**
     * The label for this sig; this name does not need to be unique.
     */
    //colorful merge, remove final
    public String          label;

    /**
     * The declaration that quantifies over each atom in this sig.
     */

    public final Decl            decl;

    /**
     * The list of "per atom" fact associated with this signature; each fact is
     * allowed to refer to this.decl.get()
     */
    private final SafeList<Expr> facts = new SafeList<Expr>();

    /**
     * Returns true if this sig is a toplevel sig (meaning: it is UNIV, or it is a
     * non-subset sig with parent==UNIV)
     */
    public final boolean isTopLevel() {
        return (this != NONE) && (this instanceof PrimSig) && (this == UNIV || ((PrimSig) this).parent == UNIV);
    }

    /** Constructs a new builtin PrimSig. */
    private Sig(String label) {
        super(Pos.UNKNOWN, null, new HashMap<Integer,Pos>()); // [HASLab] colorful Alloy
        Expr oneof = ExprUnary.Op.ONEOF.make(null, this);
        ExprVar v = ExprVar.make(null, "this", oneof.type);
        this.decl = new Decl(null, null, null, Util.asList(v), oneof);
        this.builtin = true;
        this.isAbstract = null;
        this.isLone = null;
        this.isOne = null;
        this.isSome = null;
        this.label = label;
        this.isSubset = null;
        this.isSubsig = Pos.UNKNOWN;
        this.isPrivate = null;
        this.isMeta = null;
        this.isEnum = null;
        this.attributes = ConstList.make();
    }

    /** Constructs a new PrimSig or SubsetSig. */
    // [HASLab] colorful Alloy
    private Sig(Type type, String label, Attr... attributes) throws Err {
        this(type, label, new HashMap<Integer,Pos>(), attributes);
    }

    /** Constructs a new PrimSig or SubsetSig. */
    // [HASLab] colorful Alloy
    private Sig(Type type, String label, Map<Integer,Pos> color, Attr... attributes) throws Err {
        super(AttrType.WHERE.find(attributes), type, color); // [HASLab] colorful Alloy
        this.attributes = Util.asList(attributes);
        Expr oneof = ExprUnary.Op.ONEOF.make(null, this);
        ExprVar v = ExprVar.make(null, "this", oneof.type);
        this.decl = new Decl(null, null, null, Util.asList(v), oneof);
        Pos isAbstract = null, isLone = null, isOne = null, isSome = null, isSubsig = null, isSubset = null,
                        isPrivate = null, isMeta = null, isEnum = null;
        for (Attr a : attributes)
            if (a != null)
                switch (a.type) {
                    case ABSTRACT :
                        isAbstract = a.pos.merge(isAbstract);
                        break;
                    case ENUM :
                        isEnum = a.pos.merge(isEnum);
                        break;
                    case LONE :
                        isLone = a.pos.merge(isLone);
                        break;
                    case META :
                        isMeta = a.pos.merge(isMeta);
                        break;
                    case ONE :
                        isOne = a.pos.merge(isOne);
                        break;
                    case PRIVATE :
                        isPrivate = a.pos.merge(isPrivate);
                        break;
                    case SOME :
                        isSome = a.pos.merge(isSome);
                        break;
                    case SUBSET :
                        isSubset = a.pos.merge(isSubset);
                        break;
                    case SUBSIG :
                        isSubsig = a.pos.merge(isSubsig);
                        break;
                    default :
                        //TODO throw new ErrorWarning("Undefined case " + a);
                }
        this.isPrivate = isPrivate;
        this.isMeta = isMeta;
        this.isEnum = isEnum;
        this.isAbstract = isAbstract;
        this.isLone = isLone;
        this.isOne = isOne;
        this.isSome = isSome;
        this.isSubset = isSubset;
        this.isSubsig = isSubsig;
        this.label = label;
        this.builtin = false;
        if (isLone != null && isOne != null)
            throw new ErrorSyntax(isLone.merge(isOne), "You cannot declare a sig to be both lone and one.");
        if (isLone != null && isSome != null)
            throw new ErrorSyntax(isLone.merge(isSome), "You cannot declare a sig to be both lone and some.");
        if (isOne != null && isSome != null)
            throw new ErrorSyntax(isOne.merge(isSome), "You cannot declare a sig to be both one and some.");
        if (isSubset != null && isAbstract != null)
            throw new ErrorSyntax(isAbstract, "Subset signature cannot be abstract.");
        if (isSubset != null && isSubsig != null)
            throw new ErrorSyntax(isAbstract, "Subset signature cannot be a regular subsignature.");
        //colorful Alloy

    }

    /**
     * Returns true if we can determine the two expressions are equivalent; may
     * sometimes return false.
     */
    @Override
    public boolean isSame(Expr obj) {
        Sig me = this;
        while (obj instanceof ExprUnary && ((ExprUnary) obj).op == ExprUnary.Op.NOOP)
            obj = ((ExprUnary) obj).sub;
        while (obj instanceof SubsetSig && ((SubsetSig) obj).exact && ((SubsetSig) obj).parents.size() == 1)
            obj = ((SubsetSig) obj).parents.get(0);
        while (me instanceof SubsetSig && ((SubsetSig) me).exact && ((SubsetSig) me).parents.size() == 1)
            me = ((SubsetSig) me).parents.get(0);
        return (me == obj);
    }

    /** Returns true iff "this is equal or subtype of that" */
    public abstract boolean isSameOrDescendentOf(Sig that);

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        return 1;
    }

    /**
     * Add a new per-atom fact; this expression is allowed to refer to
     * this.decl.get()
     */
    public void addFact(Expr fact) throws Err {
        if (fact.ambiguous)
            fact = fact.resolve_as_formula(null);
        if (!fact.errors.isEmpty())
            throw fact.errors.pick();
        if (!fact.type.is_bool)
            throw new ErrorType(fact.span(), "This expression must be a formula; instead its type is " + fact.type);
        facts.add(fact);
    }

    /**
     * Return the list of per-atom facts; each expression is allowed to refer to
     * this.decl.get()
     */
    public SafeList<Expr> getFacts() {
        return facts.dup();
    }

    /** {@inheritDoc} */
    @Override
    public final String getHTML() {
        return "<b>sig</b> " + label + " <i>" + type + "</i>";
    }

    /** {@inheritDoc} */
    @Override
    public final List< ? extends Browsable> getSubnodes() {
        TempList<Browsable> ans = new TempList<Browsable>();
        if (this instanceof PrimSig) {
            Sig parent = ((PrimSig) this).parent;
            if (parent != null && !parent.builtin)
                ans.add(make(parent.pos, parent.span(), "<b>extends sig</b> " + parent.label, parent.getSubnodes()));
        } else {
            ConstList<Sig> parents = ((SubsetSig) this).parents;
            for (Sig p : parents)
                ans.add(make(p.pos, p.span(), "<b>in sig</b> " + p.label, p.getSubnodes()));
        }
        for (Decl d : fields)
            for (ExprHasName v : d.names) {
                ans.add(make(v.span(), v.span(), "<b>field</b> " + v.label + " <i>" + v.type + "</i>", d.expr));
            }
        for (Expr f : facts)
            ans.add(make(f.span(), f.span(), "<b>fact</b>", f));
        return ans.makeConst();
    }

    // ==============================================================================================================//

    /**
     * Mutable; reresents a non-subset signature.
     * <p>
     * Note: except for "children()", the return value of every method is always
     * valid for all time; for example, given sigs A and B, and you call
     * C=A.intersect(B), then the result C will always be the intersection of A and
     * B even if the caller later constructs more sigs or subsigs or subsetsigs...
     */

    public static final class PrimSig extends Sig {

        /**
         * Stores its immediate children sigs (not including NONE)
         * <p>
         * Note: if this==UNIV, then this list will always be empty, since we don't keep
         * track of UNIV's children
         */
        private final SafeList<PrimSig> children = new SafeList<PrimSig>();

        /**
         * Returns its immediate children sigs (not including NONE)
         * <p>
         * Note: if this==UNIV, then this method will throw an exception, since we don't
         * keep track of UNIV's children
         */
        public SafeList<PrimSig> children() throws Err {
            if (this == UNIV)
                throw new ErrorFatal("Internal error (cannot enumerate the subsigs of UNIV)");
            return children.dup();
        }

        /**
         * Returns its subsigs and their subsigs and their subsigs, etc.
         * <p>
         * Note: if this==UNIV, then this method will throw an exception, since we don't
         * keep track of UNIV's children
         */
        public Iterable<PrimSig> descendents() throws Err {
            if (this == UNIV)
                throw new ErrorFatal("Internal error (cannot enumerate the subsigs of UNIV)");
            Iterable<PrimSig> answer = children.dup();
            for (PrimSig x : children)
                answer = Util.fastJoin(answer, x.descendents());
            return answer;
        }

        /**
         * If this is UNIV or NONE, then this field is null, else this field is the
         * parent sig.
         */
        public final PrimSig parent;

        /** Constructs a builtin PrimSig. */
        private PrimSig(String label, PrimSig parent, boolean add) {
            super(label);
            this.parent = parent;
            if (add)
                this.parent.children.add(this);
        }

        /**
         * Constructs a non-builtin sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param parent - the parent (must not be null, and must not be NONE)
         * @param attributes - the list of optional attributes such as ABSTRACT, LONE,
         *            ONE, SOME, SUBSIG, PRIVATE, META, or ENUM
         * @throws ErrorSyntax if the signature has two or more multiplicities
         * @throws ErrorType if you attempt to extend the builtin sigs NONE, SIGINT,
         *             SEQIDX, or STRING
         */
        // [HASLab] colorful Alloy
        public PrimSig(String label, PrimSig parent, Attr... attributes) throws Err {
            this(label, parent, new HashMap<Integer,Pos>(), attributes);
        }

        /**
         * Constructs a non-builtin sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param parent - the parent (must not be null, and must not be NONE)
         * @param attributes - the list of optional attributes such as ABSTRACT, LONE,
         *            ONE, SOME, SUBSIG, PRIVATE, META, or ENUM
         * @throws ErrorSyntax if the signature has two or more multiplicities
         * @throws ErrorType if you attempt to extend the builtin sigs NONE, SIGINT,
         *             SEQIDX, or STRING
         */
        // [HASLab] colorful Alloy
        public PrimSig(String label, PrimSig parent, Map<Integer,Pos> color, Attr... attributes) throws Err {
            super(((parent != null && parent.isEnum != null) ? parent.type : null), label, color, Util.append(attributes, Attr.SUBSIG)); // [HASLab] colorful Alloy
            if (parent == SIGINT)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"Int\" signature");
            if (parent == SEQIDX)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"seq/Int\" signature");
            if (parent == STRING)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"String\" signature");
            if (parent == NONE)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"none\" signature");
            if (parent == null)
                parent = UNIV;
            else if (parent != UNIV)
                parent.children.add(this);
            this.parent = parent;
            if (isEnum != null && parent != UNIV)
                throw new ErrorType(pos, "sig " + label + " is not a toplevel sig, so it cannot be an enum.");
            for (; parent != null; parent = parent.parent)
                if (parent.isEnum != null) {
                    if (parent != this.parent)
                        throw new ErrorSyntax(pos, "sig " + label + " cannot extend a signature which is an atom in an enum.");
                    if (isOne == null)
                        throw new ErrorSyntax(pos, "sig " + label + " is an atom in an enum, so it must have the \"one\" multiplicity.");
                }
        }

        /**
         * Constructs a toplevel non-builtin sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param attributes - the list of optional attributes such as ABSTRACT, LONE,
         *            ONE, SOME, SUBSIG, PRIVATE, META, or ENUM
         * @throws ErrorSyntax if the signature has two or more multiplicities
         */
        public PrimSig(String label, Attr... attributes) throws Err {
            this(label, null, attributes);
        }

        /** {@inheritDoc} */
        @Override
        public boolean isSameOrDescendentOf(Sig that) {
            if (this == NONE || this == that || that == UNIV)
                return true;
            if (this == UNIV || that == NONE)
                return false;
            for (PrimSig me = this; me != null; me = me.parent)
                if (me == that)
                    return true;
            return false;
        }

        /**
         * Returns the intersection between this and that (and returns "none" if they do
         * not intersect).
         */
        public PrimSig intersect(PrimSig that) {
            if (this.isSameOrDescendentOf(that))
                return this;
            if (that.isSameOrDescendentOf(this))
                return that;
            return NONE;
        }

        /**
         * Returns true iff the intersection between this and that is not "none".
         */
        public boolean intersects(PrimSig that) {
            if (this.isSameOrDescendentOf(that))
                return this != NONE;
            if (that.isSameOrDescendentOf(this))
                return that != NONE;
            return false;
        }

        /**
         * Returns the most-specific-sig that contains this and that. In particular, if
         * this extends that, then return that.
         */
        public PrimSig leastParent(PrimSig that) {
            if (isSameOrDescendentOf(that))
                return that;
            PrimSig me = this;
            while (true) {
                if (that.isSameOrDescendentOf(me))
                    return me;
                me = me.parent;
                if (me == null)
                    return UNIV;
            }
        }


    }

    // ==============================================================================================================//

    /** Mutable; reresents a subset signature. */

    public static final class SubsetSig extends Sig {

        /**
         * The list of Sig that it is a subset of; this list is never empty.
         */
        public final ConstList<Sig> parents;

        /**
         * If true, then this sig is EXACTLY equal to the union of its parents.
         */
        public final boolean        exact;

        /** Computes the type for this sig. */
        private static Type getType(String label, Iterable<Sig> parents) throws Err {
            Type ans = null;
            if (parents != null)
                for (Sig parent : parents) {
                    if (parent == UNIV)
                        return UNIV.type;
                    if (ans == null)
                        ans = parent.type;
                    else
                        ans = ans.unionWithCommonArity(parent.type);
                }
            return (ans != null) ? ans : (UNIV.type);
        }


        /**
         * Constructs a subset sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param parents - the list of parents (if this list is null or empty, we
         *            assume the caller means UNIV)
         * @param attributes - the list of optional attributes such as EXACT, SUBSET,
         *            LONE, ONE, SOME, PRIVATE, or META
         * @throws ErrorSyntax if the signature has two or more multiplicities
         * @throws ErrorType if parents only contains NONE
         */
        // [HASLab] colorful Alloy
        public SubsetSig(String label, Collection<Sig> parents, Attr... attributes) throws Err {
            this(label, parents, new HashMap<Integer,Pos>(), attributes);
        }

        /**
         * Constructs a subset sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param parents - the list of parents (if this list is null or empty, we
         *            assume the caller means UNIV)
         * @param attributes - the list of optional attributes such as EXACT, SUBSET,
         *            LONE, ONE, SOME, PRIVATE, or META
         * @throws ErrorSyntax if the signature has two or more multiplicities
         * @throws ErrorType if parents only contains NONE
         */
        // [HASLab] colorful Alloy
        public SubsetSig(String label, Collection<Sig> parents, Map<Integer,Pos> color, Attr... attributes) throws Err {
            super(getType(label, parents), label, color, Util.append(attributes, Attr.SUBSET)); // [HASLab] colorful Alloy

            if (isEnum != null)
                throw new ErrorType(pos, "Subset signature cannot be an enum.");
            boolean exact = false;
            for (Attr a : attributes)
                if (a != null && a.type == AttrType.EXACT)
                    exact = true;
            this.exact = exact;
            TempList<Sig> temp = new TempList<Sig>(parents == null ? 1 : parents.size());
            if (parents == null || parents.size() == 0) {
                temp.add(UNIV);
            } else {
                for (Sig parent : parents) {
                    if (!Version.experimental) {
                        if (parent == SIGINT)
                            throw new ErrorSyntax(pos, "sig " + label + " cannot be a subset of the builtin \"Int\" signature");
                        if (parent == SEQIDX)
                            throw new ErrorSyntax(pos, "sig " + label + " cannot be a subset of the builtin \"seq/Int\" signature");
                        if (parent == STRING)
                            throw new ErrorSyntax(pos, "sig " + label + " cannot be a subset of the builtin \"String\" signature");
                    }
                    if (parent == Sig.UNIV) {
                        temp.clear();
                        temp.add(UNIV);
                        break;
                    }
                    if (parent != Sig.NONE && !temp.contains(parent))
                        temp.add(parent);
                }
            }
            if (temp.size() == 0)
                throw new ErrorType(pos, "Sig " + label + " must have at least one non-empty parent.");
            this.parents = temp.makeConst();
        }

        /** {@inheritDoc} */
        @Override
        public boolean isSameOrDescendentOf(Sig that) {
            if (that == UNIV || that == this)
                return true;
            if (that == NONE)
                return false;
            for (Sig p : parents)
                if (p.isSameOrDescendentOf(that))
                    return true;
            return false;
        }


    }

    // ==============================================================================================================//

    /** Mutable; represents a field. */

    public static final class Field extends ExprHasName implements Clause {

        /** The sig that this field belongs to; never null. */
        // [HASLab] colorful Alloy, removed final
        public Sig           sig;

        /** Nonnull if the user wanted this field to be private. */
        public final Pos     isPrivate;

        /** Nonnull if this field is a meta field. */
        public final Pos     isMeta;

        /** True if this is a defined field. */
        public final boolean defined;

        /** The declaration that this field came from. */
        private Decl         decl;

        /** Return the declaration that this field came from. */
        public Decl decl() {
            return decl;
        }

        /** Constructs a new Field object. */
        // [HASLab] colorful Alloy
        private Field(Pos pos, Pos isPrivate, Pos isMeta, Pos disjoint, Pos disjoint2, Sig sig, String label, Expr bound, Map<Integer,Pos> color) throws Err {
            super(pos, label, sig.type.product(bound.type), color); // [HASLab] colorful Alloy
            this.defined = bound.mult() == ExprUnary.Op.EXACTLYOF;
            if (sig.builtin)
                throw new ErrorSyntax(pos, "Builtin sig \"" + sig + "\" cannot have fields.");
            if (!bound.errors.isEmpty())
                throw bound.errors.pick();
            if (!this.defined && bound.hasCall())
                throw new ErrorSyntax(pos, "Field \"" + label + "\" declaration cannot contain a function or predicate call.");
            if (bound.type.arity() > 0 && bound.type.hasNoTuple())
                throw new ErrorType(pos, "Cannot bind field " + label + " to the empty set or empty relation.");
            this.isPrivate = (isPrivate != null ? isPrivate : sig.isPrivate);
            this.isMeta = (isMeta != null ? isMeta : sig.isMeta);
            this.sig = sig;
        }

        /**
         * Returns a human-readable description of this field's name.
         */
        @Override
        public String toString() {
            if (sig.label.length() == 0)
                return label;
            else
                return "field (" + sig + " <: " + label + ")";
        }

        /** {@inheritDoc} */
        @Override
        public void toString(StringBuilder out, int indent) {
            if (indent < 0) {
                out.append("(").append(sig.label).append(" <: ").append(label).append(")");
            } else {
                for (int i = 0; i < indent; i++) {
                    out.append(' ');
                }
                out.append("field ").append(sig.label).append(" <: ").append(label).append(" with type=").append(type).append('\n');
            }
        }
        public void print(StringBuilder out, int indent) {
            if (indent < 0) {
                //out.append("(").append(sig.label).append(" <: ").append(label).append(")");
                out.append(label);
            } else {
                for (int i = 0; i < indent; i++) {
                    out.append(' ');
                }
                out.append("field ").append(sig.label).append(" <: ").append(label).append(" with type=").append(type).append('\n');
            }
        }


        /** {@inheritDoc} */
        @Override
        public Expr resolve(Type t, Collection<ErrorWarning> warns) {
            return this;
        }

        /** {@inheritDoc} */
        @Override
        public final <T> T accept(VisitReturn<T> visitor) throws Err {
            return visitor.visit(this);
        }

        /** {@inheritDoc} */
        @Override
        public String getHTML() {
            return "<b>field</b> " + label + " <i>" + type + "</i>";
        }

        /** {@inheritDoc} */
        @Override
        public List< ? extends Browsable> getSubnodes() {
            Expr bound = decl.expr;
            Browsable s = make(sig.pos, sig.span(), "<b>from sig</b> " + sig.label, sig.getSubnodes());
            Browsable b = make(bound.span(), bound.span(), "<b>bound</b>", bound);
            return Util.asList(s, b);
        }

        @Override
        public String explain() {

            StringBuilder sb = new StringBuilder();
            sb.append("relation ");

            if (isPrivate != null) {
                sb.append("private ");
            }
            if (isMeta != null) {
                sb.append("meta ");
            }
            sb.append(clean(label));
            sb.append(":\n");
            Table table = TableView.toTable(type);
            sb.append(table).append("\n");
            return sb.toString();
        }

        public Field mergeField(Field field,StringBuilder fact){
           Integer b=compareMergeLaw(color.keySet(), field.color.keySet());

                if(decl.expr.toString().equals(field.decl.expr.toString())){
                    if(color.keySet().equals(field.color.keySet())){
                        return this;
                    }

                    if(b!=null){
                        VisiterRemoveFeatB visiterRemoveFeatB=new VisiterRemoveFeatB();
                        visiterRemoveFeatB.setFeatB(b);
                        decl.expr=decl.expr.accept(visiterRemoveFeatB);
                        decl.color=decl.expr.color;

                        color.remove(b);
                        color.remove(-b);
                        return this;
                    }


                }else if(decl.expr instanceof ExprUnary && field.decl.expr instanceof ExprUnary){
                    ExprUnary.Op op=((ExprUnary) decl.expr).op;
                    if(!((ExprUnary) decl.expr).op.equals(((ExprUnary) field.decl.expr).op)){// 修改multiplicity
                        op= ExprUnary.Op.SETOF;
                        if(!((ExprUnary) decl.expr).op.equals(ExprUnary.Op.SETOF)){
                            StringBuilder coloF, colorB;
                            String name = "set";
                            if(((ExprUnary) decl.expr).op.equals(LONEOF))
                                name="lone";
                            else if(((ExprUnary) decl.expr).op.equals(ONEOF))
                                name="one";
                            else if(((ExprUnary) decl.expr).op.equals(SOMEOF))
                                name="some";

                            coloF = new StringBuilder();
                            colorB = new StringBuilder();
                            if (decl.expr.color != null)
                                decl.expr.printcolor(coloF, colorB);
                            fact.append("\r\n        "+coloF+"all s:"+label.substring(5)+" | "+ name+" s."+decl.names.get(0).label+colorB);
                        }
                        if(!((ExprUnary) field.decl.expr).op.equals(ExprUnary.Op.SETOF)){
                            String name = "set";
                            if(((ExprUnary) field.decl.expr).op.equals(LONEOF))
                                name="lone";
                            else if(((ExprUnary) field.decl.expr).op.equals(ONEOF))
                                name="one";
                            else if(((ExprUnary) field.decl.expr).op.equals(SOMEOF))
                                name="some";
                            StringBuilder coloF, colorB;
                            coloF = new StringBuilder();
                            colorB = new StringBuilder();
                            if (field.decl.expr.color != null)
                                field.decl.expr.printcolor(coloF, colorB);
                            fact.append("\r\n        "+coloF+"all s:"+label.substring(5)+" | "+ name+" s."+field.decl.names.get(0).label+colorB);
                        }
                    }
                    decl.color.remove(b);
                    decl.color.remove(-b);

                    Expr exprNew=ExprBinary.Op.PLUS.make(decl.expr.pos,null,((ExprUnary)decl.expr).sub,((ExprUnary) field.decl.expr).sub,decl.color);
                    exprNew=op.make(decl.expr.pos,exprNew,null,0,decl.color);
                    VisitRefactor refactor =new VisitRefactor();
                    decl.expr=exprNew.accept(refactor);

                    return this;

                }


            return null;
        }

         public String printField(){
            StringBuilder print=new StringBuilder();
             StringBuilder  coloFieldF=new StringBuilder();
             StringBuilder colorFieldB =new StringBuilder();
             if(color!=null){
                 Map<Integer,Pos> fcol=new HashMap<>(color);
                 if(color!=null)
                     for (Map.Entry<Integer,Pos> col:color.entrySet()){
                         fcol.remove(col.getKey());
                     }

                 printcolor(coloFieldF,colorFieldB,fcol.keySet());
             }
             print.append(coloFieldF);
             print.append(decl.disjoint!=null? "disj ": "");

                 print.append(label);
                 print.append(": ");

                 //get the first Field

                 VisitprintmergeExpr visitprintmergeExpr=new VisitprintmergeExpr();
                 visitprintmergeExpr.setParentFeats(decl().color.keySet());
                 print.append(decl().expr.accept(visitprintmergeExpr));
                 print.append(colorFieldB);


             return print.toString();
         }

    }

    // ==============================================================================================================//

    /** The list of fields. */
    private final SafeList<Decl>  fields     = new SafeList<Decl>();
    private final SafeList<Field> realFields = new SafeList<>();

    /**
     * Return the list of fields as a unmodifiable list of declarations (where you
     * can see which fields are declared to be disjoint)
     */
    public final SafeList<Decl> getFieldDecls() {
        return fields.dup();
    }

    /**
     * Return the list of fields as a combined unmodifiable list (without telling
     * you which fields are declared to be disjoint)
     */
    public final SafeList<Field> getFields() {
        SafeList<Field> ans = new SafeList<Field>();
        for (Decl d : fields)
            for (ExprHasName n : d.names)
                ans.add((Field) n);
        return ans.dup();
    }

    /**
     * Add then return a new field, where "all x: ThisSig | x.F in bound"
     * <p>
     * Note: the bound must be fully-typechecked and have exactly 0 free variable,
     * or have "x" as its sole free variable.
     *
     * @param label - the name of this field (it does not need to be unique)
     * @param bound - the new field will be bound by "all x: one ThisSig |
     *            x.ThisField in bound"
     * @throws ErrorSyntax if the sig is one of the builtin sig
     * @throws ErrorSyntax if the bound contains a predicate/function call
     * @throws ErrorType if the bound is not fully typechecked or is not a
     *             set/relation
     */
    public final Field addField(String label, Expr bound) throws Err {
        bound = bound.typecheck_as_set();
        if (bound.ambiguous)
            bound = bound.resolve_as_set(null);
        if (bound.mult == 0 && bound.type.arity() == 1)
            bound = ExprUnary.Op.ONEOF.make(null, bound); // If unary, and no
                                                         // multiplicity
                                                         // symbol, we assume
                                                         // it's oneOf
        final Field f = new Field(null, null, null, null, null, this, label, bound, new HashMap<Integer,Pos>()); // [HASLab] colorful Alloy
        final Decl d = new Decl(null, null, null, Arrays.asList(f), bound, new HashMap<Integer,Pos>()); // [HASLab] colorful Alloy
        f.decl = d;
        fields.add(d);
        realFields.add(f);
        return f;
    }

    /**
     * Add then return a new field, where "all x: ThisSig | x.F in bound"
     * <p>
     * Note: the bound must be fully-typechecked and have exactly 0 free variable,
     * or have "x" as its sole free variable.
     *
     * @param pos - the position in the original file where this field was defined
     *            (can be null if unknown)
     * @param isPrivate - if nonnull, that means the user intended this field to be
     *            "private"
     * @param isMeta - if nonnull, that means the user intended this field to be
     *            "meta"
     * @param labels - the names of the fields to be added (these names does not
     *            need to be unique)
     * @param bound - the new field will be bound by "all x: one ThisSig |
     *            x.ThisField in bound"
     * @throws ErrorSyntax if the sig is one of the builtin sig
     * @throws ErrorSyntax if the bound contains a predicate/function call
     * @throws ErrorType if the bound is not fully typechecked or is not a
     *             set/relation
     */
    // [HASLab] colorful Alloy
    public final Field[] addTrickyField(Pos pos, Pos isPrivate, Pos isDisjoint, Pos isDisjoint2, Pos isMeta, String[] labels, Expr bound, Map<Integer,Pos> color) throws Err {
        bound = bound.typecheck_as_set();
        if (bound.ambiguous)
            bound = bound.resolve_as_set(null);
        if (bound.mult == 0 && bound.type.arity() == 1)
            bound = ExprUnary.Op.ONEOF.make(null, bound); // If unary, and no
                                                         // multiplicity
                                                         // symbol, we assume
                                                         // it's oneOf
        final Field[] f = new Field[labels.length];
        for (int i = 0; i < f.length; i++)
            f[i] = new Field(pos, isPrivate, isMeta, isDisjoint, isDisjoint2, this, labels[i], bound, color); // [HASLab] colorful Alloy
        final Decl d = new Decl(isPrivate, isDisjoint, isDisjoint2, Arrays.asList(f), bound, color); // [HASLab] colorful Alloy
        for (int i = 0; i < f.length; i++) {
            f[i].decl = d;
            realFields.add(f[i]);
        }
        fields.add(d);
        return f;
    }

    /**
     * Add then return a new field F where this.F is bound to an exact "definition"
     * expression.
     * <p>
     * Note: the definition must be fully-typechecked and have exactly 0 free
     * variables.
     * <p>
     * Note: currently the defined field must consist product and union operators
     * over sigs.
     *
     * @param pos - the position in the original file where this field was defined
     *            (can be null if unknown)
     * @param isPrivate - if nonnull, that means this field should be marked as
     *            private
     * @param isMeta - if nonnull, that means this field should be marked as meta
     * @param label - the name of this field (it does not need to be unique)
     * @param bound - the new field will be defined to be exactly equal to
     *            sig.product(definition)
     * @throws ErrorSyntax if the sig is one of the builtin sig
     * @throws ErrorSyntax if the bound contains a predicate/function call
     * @throws ErrorType if the bound is not fully typechecked or is not a
     *             set/relation
     */
    public final Field addDefinedField(Pos pos, Pos isPrivate, Pos isMeta, String label, Expr bound) throws Err {
        bound = bound.typecheck_as_set();
        if (bound.ambiguous)
            bound = bound.resolve_as_set(null);
        if (bound.mult() != ExprUnary.Op.EXACTLYOF)
            bound = ExprUnary.Op.EXACTLYOF.make(null, bound);
        final Field f = new Field(pos, isPrivate, isMeta, null, null, this, label, bound, new HashMap<Integer,Pos>()); // [HASLab] colorful Alloy
        final Decl d = new Decl(null, null, null, Arrays.asList(f), bound, new HashMap<Integer,Pos>()); // [HASLab] colorful Alloy
        f.decl = d;
        fields.add(d);
        realFields.add(f);
        return f;
    }

    @Override
    public String explain() {
        Table t = new Table(2, 1 + realFields.size(), 1);

        StringBuilder sb = new StringBuilder();
        if (builtin)
            sb.append("builtin ");
        if (isEnum != null)
            sb.append("enum ");
        if (isAbstract != null)
            sb.append("abstract ");
        if (isLone != null)
            sb.append("lone ");
        if (isOne != null)
            sb.append("one ");
        if (isMeta != null)
            sb.append("meta ");
        if (isSome != null)
            sb.append("some ");
        if (isSubsig != null)
            sb.append("sig ");
        if (isSubset != null)
            sb.append("subset ");
        t.set(0, 0, sb);
        t.set(1, 0, clean(label));

        int n = 1;
        for (Field f : realFields) {
            t.set(0, n++, clean(f.label));
        }
        n = 1;
        for (Field f : realFields) {
            String relation = clean(type.join(f.type).toString());
            Table table = TableView.toTable(relation, false);
            t.set(1, n++, table);
        }

        return t.toString();
    }

    //colorful merge
    /**
     * merge top-level sigs, merge this with sig
     * ( a b sig n { ds0,...,dsk}ba,  a -b sig n { ds′0,...,ds′l}-b a) =
     * a sig n {b ds0 b,...,b dsk b, b ds′0 b,...,b ds′l b } a
     * @param sig   Sig to be merge
     * @param fact store facts if the quantifier need to be removed
     * @param b  feature to be remove
     */
    public Sig mergeSig(Sig sig,Integer b,StringBuilder fact){
        //used to generate new Sig
        Attr[] attributes = new Attr[this.attributes.size()];
        for (int i = 0; i < this.attributes.size(); i++) {
            attributes[i] = this.attributes.get(i);
        }
        Sig signew=null;
        if(this instanceof Sig.PrimSig)
            signew = new Sig.PrimSig(label, ((Sig.PrimSig) this).parent, attributes);
        else if (this instanceof Sig.SubsetSig)
            signew=new Sig.SubsetSig(label,((Sig.SubsetSig) this).parents,attributes);

        Map<Integer,Pos> feats=new HashMap<>(color);
        feats.remove(b);
        feats.remove(-b);
        signew.color.putAll(feats);

        //add feature b or -b to fields.
       // Sig finalSignew = signew;
        VisitOld2new sigold2newVisitor = new VisitOld2new();
        //sigold2newVisitor.getSigOld2new();
        sigold2newVisitor.getSigOld2new().put(this,signew);
        sigold2newVisitor.getSigOld2new().put(sig,signew);

        for (Decl d: getFieldDecls()){
            Expr exprNew=d.expr.accept(sigold2newVisitor);
            String[]labels = new String[d.names.size()];
            for(int i=0; i< d.names.size();i++){
                labels[i]=d.names.get(i).label;
            }
            signew.addTrickyField(d.span(),d.isPrivate,d.disjoint,d.disjoint2,null,labels,exprNew,d.color);
        }
        for (Decl d: sig.getFieldDecls()){
            Expr exprNew=d.expr.accept(sigold2newVisitor);
            String[]labels = new String[d.names.size()];
            for(int i=0; i< d.names.size();i++){
                labels[i]=d.names.get(i).label;
            }
            signew.addTrickyField(d.span(),d.isPrivate,d.disjoint,d.disjoint2,null,labels,exprNew,d.color);
        }

        Sig sigBinaryField=signew.mergeField(fact);

        return sigBinaryField;

    }
    //colorful merge
    /**
     * merge all fields for a sig
     * @param
     * @return
     */
    public Sig mergeField(StringBuilder fact) {
        VisitOld2new sigOld2new = new VisitOld2new();
        Integer b;
        //used to generate new Sig
        Attr[] attributes = new Attr[this.attributes.size()];
        for (int i = 0; i < this.attributes.size(); i++) {
            attributes[i] = this.attributes.get(i);
        }
        Sig signew=null;
        if(this instanceof Sig.PrimSig)
            signew = new Sig.PrimSig(label, ((Sig.PrimSig) this).parent, attributes);
        else if (this instanceof Sig.SubsetSig)
            signew=new Sig.SubsetSig(label,((Sig.SubsetSig) this).parents,attributes);
        signew.color=color;
        sigOld2new.getSigOld2new().put(this,signew);


        //prepare the order of features
        Set<Integer> temp=new HashSet<>();
        for(Integer i: CompModule.feats)
            temp.add(i>0? i: -i);
        Set <Integer> feat=new TreeSet<>(temp);

        //merge Field with order of colors
        List<Decl> clone=getFieldDecls().makeCopy();
        for(Integer curMergFeat: feat){
            ArrayList<Decl> fieldVisited=new ArrayList<>();
            List<Decl> clonetemp=new ArrayList<>(clone);
            for(Decl d: clonetemp){
                if (fieldVisited.contains(d)) continue;
                fieldVisited.add(d);

                for(Decl d2: clonetemp){
                    if (fieldVisited.contains(d2)) continue;
                    if (d.names.get(0).label.equals(d2.names.get(0).label)) {
                        b=compareMergeLaw(d.color.keySet(), d2.color.keySet());

                        if (b==curMergFeat) {
                           // if(d.expr.toString().equals(d2.expr.toString())){
                              //  fieldVisited.add(d2);
                              //  VisiterRemoveFeatB visiterRemoveFeatB=new VisiterRemoveFeatB();
                             //   visiterRemoveFeatB.setFeatB(b);
                             //   d.expr=d.expr.accept(visiterRemoveFeatB);
                             //   d.color=d.expr.color;
                              //  clone.remove(d2);

                           // }else
                                if(d.expr instanceof ExprUnary && d2.expr instanceof ExprUnary){
                                fieldVisited.add(d2);

                                ExprUnary.Op op=((ExprUnary) d.expr).op;
                                if(!((ExprUnary) d.expr).op.equals(((ExprUnary) d2.expr).op)){// 修改multiplicity
                                    op= ExprUnary.Op.SETOF;
                                    if(!((ExprUnary) d.expr).op.equals(ExprUnary.Op.SETOF)){
                                        StringBuilder coloF, colorB;
                                        String name = "set";
                                        if(((ExprUnary) d.expr).op.equals(LONEOF))
                                            name="lone";
                                        else if(((ExprUnary) d.expr).op.equals(ONEOF))
                                            name="one";
                                        else if(((ExprUnary) d.expr).op.equals(SOMEOF))
                                            name="some";

                                        coloF = new StringBuilder();
                                        colorB = new StringBuilder();
                                        if (d.expr.color != null)
                                            d.expr.printcolor(coloF, colorB);
                                        fact.append("\r\nfact RemoveQualtifier {\r\n      "+coloF+"all s:"+label.substring(5)+" | "+ name+" s."+d.names.get(0).label+colorB +"\r\n        }");
                                    }
                                    if(!((ExprUnary) d2.expr).op.equals(ExprUnary.Op.SETOF)){
                                        String name = "set";
                                        if(((ExprUnary) d2.expr).op.equals(LONEOF))
                                            name="lone";
                                        else if(((ExprUnary) d2.expr).op.equals(ONEOF))
                                            name="one";
                                        else if(((ExprUnary) d2.expr).op.equals(SOMEOF))
                                            name="some";
                                        StringBuilder coloF, colorB;
                                        coloF = new StringBuilder();
                                        colorB = new StringBuilder();
                                        if (d2.expr.color != null)
                                            d2.expr.printcolor(coloF, colorB);
                                        fact.append("\r\nfact RemoveQualtifier {\r\n        "+coloF+"all s:"+label.substring(5)+" | "+ name+" s."+d2.names.get(0).label+colorB+"\r\n        }");
                                    }
                                }
                                d.color.remove(b);
                                d.color.remove(-b);

                                Expr exprNew=ExprBinary.Op.PLUS.make(d.expr.pos,null,((ExprUnary)d.expr).sub,((ExprUnary) d2.expr).sub,d.color);
                                exprNew=op.make(d.expr.pos,exprNew,null,0,d.color);
                                VisitRefactor refactor =new VisitRefactor();
                                d.expr=exprNew.accept(refactor);
                                clone.remove(d2);
                            }else if(d.expr.type().arity()==d2.expr.type().arity()){
                                fieldVisited.add(d2);
                                d.color.remove(b);
                                d.color.remove(-b);
                                Expr exprNew=ExprBinary.Op.PLUS.make(d.expr.pos,null,d.expr, d2.expr,d.color);
                                VisitRefactor refactor =new VisitRefactor();
                                d.expr=exprNew.accept(refactor);
                                clone.remove(d2);
                                }
                        }
                    }
                }
            }
        }

        //add Field to new sig
        for(Decl d: clone){
            String[] labels = new String[d.names.size()];
            for (int i = 0; i < d.names.size(); i++) {
                labels[i] = d.names.get(i).label; }
            Expr exprNew = d.expr.accept(sigOld2new);
            signew.addTrickyField(d.span(), d.isPrivate, d.disjoint, d.disjoint2, null, labels, exprNew, d.color);
        }
        return signew;
    }

    //colorful merge
    public void addSomeFact(StringBuilder sigfact) {
        StringBuilder coloF, colorB;
        coloF = new StringBuilder();
        colorB = new StringBuilder();
        if (color != null)
             printcolor(coloF, colorB);

        sigfact.append("\r\n      "+coloF+"some "+ label.substring(5)+colorB);
    }
    //colorful merge
    public void addOneFact(StringBuilder sigfact) {
        StringBuilder coloF, colorB;
        coloF = new StringBuilder();
        colorB = new StringBuilder();
        if (color != null)
            printcolor(coloF, colorB);

        sigfact.append("\r\n      "+coloF+"one "+ label.substring(5)+colorB);
    }
    //colorful merge
    public void addLoneFact(StringBuilder sigfact) {
        StringBuilder coloF, colorB;
        coloF = new StringBuilder();
        colorB = new StringBuilder();
        if (color != null)
            printcolor(coloF, colorB);

        sigfact.append("\r\n      "+coloF+"lone "+ label.substring(5)+colorB);
    }
    //colorful merge
    public void addAbstractFact(SafeList<Sig> sigSafeList, StringBuilder sigfact) {
        Set<Sig> children = new HashSet<>();
        for (Sig s : sigSafeList) {
            if (!s.equals(this)) {
                if (s instanceof Sig.PrimSig) {
                    if (((Sig.PrimSig) s).parent.equals(this)) {
                        children.add(s);
                    }
                }
            }
        }

        StringBuilder coloF, colorB;
        coloF = new StringBuilder();
        colorB = new StringBuilder();
        if (color != null)
            printcolor(coloF, colorB);

        if (children.isEmpty())
            sigfact.append("\r\n      " + coloF + "no " + label.substring(5) + colorB);
        else {
            StringBuilder childString = new StringBuilder();
            for (Sig child : children) {
                childString.append(child.label.substring(5) + "+");
            }
            childString.deleteCharAt(childString.length() - 1);
            sigfact.append("\r\n      " + coloF + label.substring(5) + "=" + childString + colorB);
        }

    }
    //colorful merge
    public void printSig(StringBuilder print){
        StringBuilder coloF,colorB,coloFieldF,colorFieldB;
        coloF=new StringBuilder();
        colorB=new StringBuilder();
        if(color!=null)
            printcolor(coloF,colorB);

        print.append(coloF);

        if(isAbstract!=null)
            print.append("abstract ");
        if(isLone !=null)
            print.append("lone ");
        if (isOne!=null)
            print.append("one ");
        if(isSome != null)
            print.append("some ");

        print.append("sig "+ label.substring(5));

        if(isSubsig!=null ){
            if(((Sig.PrimSig) this).parent!=UNIV){
                print.append(" extends ");
                print.append( ((Sig.PrimSig) this).parent.label.substring(5));
            }
        }

        if(isSubset!=null){
            print.append(" in ");
            print.append(((Sig.SubsetSig) this).parents.get(0).label.substring(5));

            if(((Sig.SubsetSig) this).parents.size()>1){
                for (int j = 1; j< ((Sig.SubsetSig) this).parents.size()-1; j ++){
                    print.append(" + "+((Sig.SubsetSig) this).parents.get(j).label.substring(5));
                }
            }
        }
        //print fields
        print.append("{ ");

        for (Decl f:getFieldDecls()){
            coloFieldF=new StringBuilder();
            colorFieldB =new StringBuilder();
            if(f.color!=null){
                Map<Integer,Pos> fcol=new HashMap<>(f.color);
                if(color!=null)
                    for (Map.Entry<Integer,Pos> col:color.entrySet()){
                        fcol.remove(col.getKey());
                    }

                printcolor(coloFieldF,colorFieldB,fcol.keySet());
            }
            print.append("\r\n        "+coloFieldF);
            print.append(f.disjoint!=null? "disj ": "");
            if(f.names.size()>=1){
                for(ExprHasName n:f.names){
                    print.append(n.label+",");
                }
                print.deleteCharAt(print.length()-1);
                print.append(": ");

                //get the first Field
                Sig.Field n= (Sig.Field)f.names.get(0);
                VisitprintmergeExpr visitprintmergeExpr=new VisitprintmergeExpr();
                visitprintmergeExpr.setParentFeats(n.decl().color.keySet());
                print.append(n.decl().expr.accept(visitprintmergeExpr));
                print.append(colorFieldB);
                print.append(",");
            }
        }

        if(!getFieldDecls().isEmpty()){
            print.deleteCharAt(print.length()-1);
            //} of Sig
            print.append("\r\n        }");
        }else
            //} of Sig
            print.append("}");

        //fact for sig
        if(!getFacts().isEmpty()){
            print.append("{");
            for(Expr fact:getFacts()){
                String temp=fact.toString();
                //replace "s.fileld" to field
                temp=temp.replace(label.substring(5)+" .","");
                print.append("\r\n        "+temp);
            }
            print.append("\r\n        }\r\n");
        }

        print.append(colorB);
        print.append("\r\n");

    }
    //colorful merge
    private class VisitOld2new extends VisitReturn<Expr> {
        public Map<Sig, Sig> getSigOld2new() {
            return sigOld2new;
        }

        public Map<Field, Field> getFieldOld2new() {
            return fieldOld2new;
        }

        public void setSigOld2new(Map<Sig, Sig> sigOld2new) {
            this.sigOld2new = sigOld2new;
        }

        public void setFieldOld2new(Map<Field, Field> fieldOld2new) {
            this.fieldOld2new = fieldOld2new;
        }

        Map<Sig,Sig> sigOld2new =new HashMap();
        Map<Field,Field> fieldOld2new=new HashMap();
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
            if(sigOld2new.containsKey(x))
                return sigOld2new.get(x);

            return x;
        }

        @Override
        public Expr visit(Field x) throws Err {
            if(fieldOld2new.containsKey(x))
                return fieldOld2new.get(x);
            return x;
        }

    }
}
