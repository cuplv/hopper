package casts.InstrOpcodeIndexSensitivePiecewiseRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {
    
    static class Instr {
	static final int NONE = 0, FOO = 1, BAR = 2, OBJ = 3;
	static int[] opcxMap = new int[]{ NONE, FOO, BAR, OBJ};
	int opcode;
	Object operand;

	public Instr(int opcode, Object operand) {
	    this.opcode = opcode;
	    this.operand = operand;
	}
	public Instr(int input) {
	    int opc = makeOpc(input);
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

	int makeOpc(int input) {
	    return input << 3 + 2 * 7;
	}

	public static Instr getInstr0() {
	    return new Instr(0);	
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