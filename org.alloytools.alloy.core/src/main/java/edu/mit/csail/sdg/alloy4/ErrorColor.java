package edu.mit.csail.sdg.alloy4;

public class ErrorColor extends Err{


    /** This ensures this class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * Constructs a new color marked error.
     *
     * @param msg - the actual error message (can be null)
     */
    public ErrorColor(String msg) {
        super(null, msg, null);
    }

    /**
     * Constructs a new color marked error with "cause" as the underlying cause.
     *
     * @param msg - the actual error message (can be null)
     * @param cause - if nonnull, it is the cause of this exception
     */
    public ErrorColor(String msg, Throwable cause) {
        super(null, msg, cause);
    }

    /**
     * Constructs a new color marked error.
     *
     * @param pos - the filename/line/row information (can be null if unknown)
     * @param msg - the actual error message (can be null)
     */
    public ErrorColor(Pos pos, String msg) {
        super(pos, msg, null);
    }

    /** Returns a textual description of the error. */
    @Override
    public String toString() {
        if (pos == Pos.UNKNOWN)
            return "Feature paint error:\n" + msg;
        if (pos.filename.length() > 0)
            return "Feature paint error in " + pos.filename + " at line " + pos.y + " column " + pos.x + ":\n" + msg;
        return "Feature paint error at line " + pos.y + " column " + pos.x + ":\n" + msg;
    }
}
