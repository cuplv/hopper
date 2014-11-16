package casts.InstrOpcodeIndexSensitivePiecewiseNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {
    
    static class Instr {
	static final int NONE = 0, FOO = 1, BAR = 2, OBJ = 3;
	// only difference from refutable version is that order of FOO and BAR are switched in this array
	static int[] opcxMap = new int[]{ NONE, BAR, FOO, OBJ};
	int opcode;
	Object operand;

	public Instr(int opcode, Object operand) {
	    this.opcode = opcode;
	    this.operand = operand;
	}
	public Instr(int opc) {
	    switch (opc) {
	    case 1:
		this.operand = new Foo();
		break;
	    case 2:
		this.operand = new Bar();
		break;
	    case 3:
		this.operand = new Object();
		break;
	    default:
		break;
	    }
	    this.opcode = opcxMap[opc];
	}

	public static Instr getInstr0() {
	    return new Instr(BAR);	
	}

	public static Instr getInstr1() {
	    return new Instr(OBJ, new Object());	
	}
    }


    public static void main(String[] args) {
	List<Instr> lst = new LinkedList<Instr>();
	lst.add(Instr.getInstr0());
	lst.add(Instr.getInstr1());
	//Instr i = Instr.getInstr0();
	for (Instr i : lst) {

	    if (i.opcode == Instr.FOO) {
		Foo f = (Foo) i.operand;
	    }
	}
    }

   

    public static int getInt() {
	return 1;
    }
}