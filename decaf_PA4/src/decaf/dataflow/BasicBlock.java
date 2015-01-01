package decaf.dataflow;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.HashSet;

import decaf.machdesc.Asm;
import decaf.machdesc.Register;
import decaf.tac.Label;
import decaf.tac.Tac;
import decaf.tac.Temp;

class DefRefPoint {
	public Temp var;

	public Integer globalNum;

	public DefRefPoint(Temp var1, Integer globalNum1) {
		var = var1;
		globalNum = globalNum1;
	}

	public static final Comparator<DefRefPoint> TEMP_COMPARATOR = new Comparator<DefRefPoint>() {

		@Override
		public int compare(DefRefPoint o1, DefRefPoint o2) {
			int varCompare = Temp.ID_COMPARATOR.compare(o1.var, o2.var);
			if (varCompare != 0) {
				return varCompare;
			} else {
				return o1.globalNum > o2.globalNum ? 1 : o1.globalNum == o2.globalNum ? 0 : -1;
			}
		}
	};

	public static final Comparator<DefRefPoint> INDEX_COMPARATOR = new Comparator<DefRefPoint>() {

		@Override
		public int compare(DefRefPoint o1, DefRefPoint o2) {

			if (o1.globalNum != o2.globalNum) {
				return o1.globalNum > o2.globalNum ? 1 : -1;
			} else {
				return Temp.ID_COMPARATOR.compare(o1.var, o2.var);
			}
		}
	};
	
	public String toString() {
		return "(" + var.name + ", " + globalNum.toString() + ")";
	};
}

public class BasicBlock {
	public int bbNum;

	public enum EndKind {
		BY_BRANCH, BY_BEQZ, BY_BNEZ, BY_RETURN
	}

	public EndKind endKind;

	public int inDegree;

	public Tac tacList;

	public Label label;

	public Temp var;

	public Register varReg;

	public int[] next;
	
	public boolean cancelled;

	public boolean mark;

	public Set<Temp> def;

	public Set<Temp> liveUse;

	public Set<Temp> liveIn;

	public Set<Temp> liveOut;

	public Set<DefRefPoint> in;

	public Set<DefRefPoint> out;

	public Set<DefRefPoint> gen;

	public Set<DefRefPoint> kill;

	public Set<Integer> prev;

	public Map<DefRefPoint, List<Integer>> udChain;

	private Hashtable<Temp, ArrayList<Integer>> inAll;

	private Hashtable<Temp, Integer> newGenPointInBlock;

	public Set<Temp> saves;

	private List<Asm> asms;

	public BasicBlock() {
		def = new TreeSet<Temp>(Temp.ID_COMPARATOR);
		liveUse = new TreeSet<Temp>(Temp.ID_COMPARATOR);
		liveIn = new TreeSet<Temp>(Temp.ID_COMPARATOR);
		liveOut = new TreeSet<Temp>(Temp.ID_COMPARATOR);
		in = new TreeSet<DefRefPoint>(DefRefPoint.TEMP_COMPARATOR);
		out = new TreeSet<DefRefPoint>(DefRefPoint.TEMP_COMPARATOR);
		gen = new TreeSet<DefRefPoint>(DefRefPoint.TEMP_COMPARATOR);
		kill = new TreeSet<DefRefPoint>(DefRefPoint.TEMP_COMPARATOR);
		prev = new TreeSet<Integer>();
		udChain = new TreeMap<DefRefPoint, List<Integer>>(DefRefPoint.INDEX_COMPARATOR);
		newGenPointInBlock = new Hashtable<Temp, Integer>();
		inAll = new Hashtable<Temp, ArrayList<Integer>>();
		next = new int[2];
		asms = new ArrayList<Asm>();
	}

	public void computeDefAndLiveUse() {
		newGenPointInBlock.clear();
		for (Tac tac = tacList; tac != null; tac = tac.next) {
			switch (tac.opc) {
			case ADD:
			case SUB:
			case MUL:
			case DIV:
			case MOD:
			case LAND:
			case LOR:
			case GTR:
			case GEQ:
			case EQU:
			case NEQ:
			case LEQ:
			case LES:
				/* use op1 and op2, def op0 */
				newGenPointInBlock.put(tac.op0, tac.globalNum);
				if (tac.op1.lastVisitedBB != bbNum) {
					liveUse.add (tac.op1);
					tac.op1.lastVisitedBB = bbNum;
				}
				if (tac.op2.lastVisitedBB != bbNum) {
					liveUse.add (tac.op2);
					tac.op2.lastVisitedBB = bbNum;
				}
				if (tac.op0.lastVisitedBB != bbNum) {
					def.add (tac.op0);
					tac.op0.lastVisitedBB = bbNum;
				}
				break;
			case NEG:
			case LNOT:
			case ASSIGN:
			case INDIRECT_CALL:
			case LOAD:
				/* use op1, def op0 */
				if (tac.op1.lastVisitedBB != bbNum) {
					liveUse.add (tac.op1);
					tac.op1.lastVisitedBB = bbNum;
				}
				if (tac.op0 != null) {  // in INDIRECT_CALL with return type VOID,
										// tac.op0 is null
					newGenPointInBlock.put(tac.op0, tac.globalNum);
					if (tac.op0.lastVisitedBB != bbNum) {
						def.add (tac.op0);
						tac.op0.lastVisitedBB = bbNum;						
					}
				}
				break;
			case LOAD_VTBL:
			case DIRECT_CALL:
			case RETURN:
			case LOAD_STR_CONST:
			case LOAD_IMM4:
				/* def op0 */
				if (tac.op0 != null) {  // in DIRECT_CALL with return type VOID,
										// tac.op0 is null
					newGenPointInBlock.put(tac.op0, tac.globalNum);
					if (tac.op0.lastVisitedBB != bbNum) {
						def.add (tac.op0);
						tac.op0.lastVisitedBB = bbNum;						
					}
				}
				break;
			case STORE:
				/* use op0 and op1*/
				if (tac.op0.lastVisitedBB != bbNum) {
					liveUse.add (tac.op0);
					tac.op0.lastVisitedBB = bbNum;
				}
				if (tac.op1.lastVisitedBB != bbNum) {
					liveUse.add (tac.op1);
					tac.op1.lastVisitedBB = bbNum;
				}
				break;
			case PARM:
				/* use op0 */
				if (tac.op0.lastVisitedBB != bbNum) {
					liveUse.add (tac.op0);
					tac.op0.lastVisitedBB = bbNum;
				}
				break;
			default:
				/* BRANCH MEMO MARK PARM*/
				break;
			}
		}
		if (var != null && var.lastVisitedBB != bbNum) {
			liveUse.add (var);
			var.lastVisitedBB = bbNum;
		}
		liveIn.addAll (liveUse);
		Iterator<Temp> itr = newGenPointInBlock.keySet().iterator();
		while(itr.hasNext()){ 
			Temp key = itr.next(); 
			Integer defPlace = newGenPointInBlock.get(key); 
			gen.add(new DefRefPoint(key, defPlace));
		} 
	}
	
	private void calSingleUseDefChain(DefRefPoint refPoint) {
		ArrayList<Integer> defPoint = new ArrayList<>();
		if (newGenPointInBlock.containsKey(refPoint.var)) {
			defPoint.add(newGenPointInBlock.get(refPoint.var));
			udChain.put(refPoint, defPoint);
		} else {
			if(inAll.containsKey(refPoint.var))
				udChain.put(refPoint, inAll.get(refPoint.var));
			else
				udChain.put(refPoint, defPoint);
		}
	}

	public void calUseDefChain() {
		newGenPointInBlock.clear();
		for (DefRefPoint point : in) {
			if (!inAll.containsKey(point.var)) {
				ArrayList<Integer> defPlaceNum = new ArrayList<Integer>();
				defPlaceNum.add(point.globalNum);
				inAll.put(point.var, defPlaceNum);
			} else {
				inAll.get(point.var).add(point.globalNum);
			}
		}
		newGenPointInBlock = new Hashtable<Temp, Integer>();
		int endNum = -1;
		for (Tac tac = tacList; tac != null; tac = tac.next) {
			endNum = tac.globalNum;
			switch (tac.opc) {
			case ADD:
			case SUB:
			case MUL:
			case DIV:
			case MOD:
			case LAND:
			case LOR:
			case GTR:
			case GEQ:
			case EQU:
			case NEQ:
			case LEQ:
			case LES:
				/* use op1 and op2, def op0 */
				calSingleUseDefChain(new DefRefPoint(tac.op1, tac.globalNum));
				calSingleUseDefChain(new DefRefPoint(tac.op2, tac.globalNum));
				newGenPointInBlock.put(tac.op0, tac.globalNum);
				break;
			case NEG:
			case LNOT:
			case ASSIGN:
			case INDIRECT_CALL:
			case LOAD:
				/* use op1, def op0 */
				calSingleUseDefChain(new DefRefPoint(tac.op1, tac.globalNum));
				if (tac.op0 != null) { 
					newGenPointInBlock.put(tac.op0, tac.globalNum);
				}
				break;
			case LOAD_VTBL:
			case DIRECT_CALL:
			case RETURN:
			case LOAD_STR_CONST:
			case LOAD_IMM4:
				/* def op0 */
				if (tac.op0 != null) { 
					// in DIRECT_CALL with return type VOID, tac.op0 is null
					newGenPointInBlock.put(tac.op0, tac.globalNum);
				}
				break;
			case STORE:
				/* use op0 and op1*/
				calSingleUseDefChain(new DefRefPoint(tac.op0, tac.globalNum));
				calSingleUseDefChain(new DefRefPoint(tac.op1, tac.globalNum));
				break;
			case PARM:
				/* use op0 */
				calSingleUseDefChain(new DefRefPoint(tac.op0, tac.globalNum));
				break;
			default:
				/* BRANCH MEMO MARK PARM*/
				break;
			}
		}
		if (var != null) {
			endNum ++;
			calSingleUseDefChain(new DefRefPoint(var, endNum));
		}
	}
	public void analyzeLiveness() {
		if (tacList == null)
			return;
		Tac tac = tacList;
		for (; tac.next != null; tac = tac.next); 

		tac.liveOut = new HashSet<Temp> (liveOut);
		if (var != null)
			tac.liveOut.add (var);
		for (; tac != tacList; tac = tac.prev) {
			tac.prev.liveOut = new HashSet<Temp> (tac.liveOut);
			switch (tac.opc) {
			case ADD:
			case SUB:
			case MUL:
			case DIV:
			case MOD:
			case LAND:
			case LOR:
			case GTR:
			case GEQ:
			case EQU:
			case NEQ:
			case LEQ:
			case LES:
				/* use op1 and op2, def op0 */
				tac.prev.liveOut.remove (tac.op0);
				tac.prev.liveOut.add (tac.op1);
				tac.prev.liveOut.add (tac.op2);
				break;
			case NEG:
			case LNOT:
			case ASSIGN:
			case INDIRECT_CALL:
			case LOAD:
				/* use op1, def op0 */
				tac.prev.liveOut.remove (tac.op0);
				tac.prev.liveOut.add (tac.op1);
				break;
			case LOAD_VTBL:
			case DIRECT_CALL:
			case RETURN:
			case LOAD_STR_CONST:
			case LOAD_IMM4:
				/* def op0 */
				tac.prev.liveOut.remove (tac.op0);
				break;
			case STORE:
				/* use op0 and op1*/
				tac.prev.liveOut.add (tac.op0);
				tac.prev.liveOut.add (tac.op1);
				break;
			case BEQZ:
			case BNEZ:
			case PARM:
				/* use op0 */
				tac.prev.liveOut.add (tac.op0);
				break;
			default:
				/* BRANCH MEMO MARK PARM*/
				break;
			}
		}
	}

	public void printTo(PrintWriter pw) {
		pw.println("BASIC BLOCK " + bbNum + " : ");
		for (Tac t = tacList; t != null; t = t.next) {
			pw.println("    " + t);
		}
		switch (endKind) {
		case BY_BRANCH:
			pw.println("END BY BRANCH, goto " + next[0]);
			break;
		case BY_BEQZ:
			pw.println("END BY BEQZ, if " + var.name + " = ");
			pw.println("    0 : goto " + next[0] + "; 1 : goto " + next[1]);
			break;
		case BY_BNEZ:
			pw.println("END BY BGTZ, if " + var.name + " = ");
			pw.println("    1 : goto " + next[0] + "; 0 : goto " + next[1]);
			break;
		case BY_RETURN:
			if (var != null) {
				pw.println("END BY RETURN, result = " + var.name);
			} else {
				pw.println("END BY RETURN, void result");
			}
			break;
		}
	}

	public void printLivenessTo(PrintWriter pw) {
		pw.println("BASIC BLOCK " + bbNum + " : ");
		pw.println("  Def     = " + toString(def));
		pw.println("  liveUse = " + toString(liveUse));
		pw.println("  liveIn  = " + toString(liveIn));
		pw.println("  liveOut = " + toString(liveOut));

		for (Tac t = tacList; t != null; t = t.next) {
			pw.println("    " + t + " " + toString(t.liveOut));
		}

		switch (endKind) {
		case BY_BRANCH:
			pw.println("END BY BRANCH, goto " + next[0]);
			break;
		case BY_BEQZ:
			pw.println("END BY BEQZ, if " + var.name + " = ");
			pw.println("    0 : goto " + next[0] + "; 1 : goto " + next[1]);
			break;
		case BY_BNEZ:
			pw.println("END BY BGTZ, if " + var.name + " = ");
			pw.println("    1 : goto " + next[0] + "; 0 : goto " + next[1]);
			break;
		case BY_RETURN:
			if (var != null) {
				pw.println("END BY RETURN, result = " + var.name);
			} else {
				pw.println("END BY RETURN, void result");
			}
			break;
		}
	}

	private String udChainToString() {
		Iterator<DefRefPoint> itr = udChain.keySet().iterator();
		String output = "";
		while(itr.hasNext()){ 
			DefRefPoint key = itr.next();
			output += "    " + key.toString() + ": " + udChain.get(key).toString() + "\n";
		}
		return output;
	}

	public void printUDChainTo(PrintWriter pw) {
		pw.println("BASIC BLOCK " + bbNum + " : ");
		int endNum = -1;
		for (Tac t = tacList; t != null; t = t.next) {
			pw.println("    " + t.globalNum + ": " + t);
			endNum = t.globalNum;
		}
		endNum ++;
		pw.print("    " + endNum + ": ");
		switch (endKind) {
		case BY_BRANCH:
			pw.println("END BY BRANCH, goto " + next[0]);
			break;
		case BY_BEQZ:
			pw.print("END BY BEQZ, if " + var.name + " = ");
			pw.println("0 : goto " + next[0] + "; 1 : goto " + next[1]);
			break;
		case BY_BNEZ:
			pw.print("END BY BGTZ, if " + var.name + " = ");
			pw.println("1 : goto " + next[0] + "; 0 : goto " + next[1]);
			break;
		case BY_RETURN:
			if (var != null) {
				pw.println("END BY RETURN, result = " + var.name);
			} else {
				pw.println("END BY RETURN, void result");
			}
			break;
		}
		pw.println("  Use-Def Chain : ");
		pw.println(udChainToString());
	}

	public String toString(Set<Temp> set) {
		StringBuilder sb = new StringBuilder("[ ");
		for (Temp t : set) {
			sb.append(t.name + " ");
		}
		sb.append(']');
		return sb.toString();
	}

	public void insertBefore(Tac insert, Tac base) {
		if (base == tacList) {
			tacList = insert;
		} else {
			base.prev.next = insert;
		}
		insert.prev = base.prev;
		base.prev = insert;
		insert.next = base;
	}

	public void insertAfter(Tac insert, Tac base) {
		if (tacList == null) {
			tacList = insert;
			insert.next = null;
			return;
		}
		if (base.next != null) {
			base.next.prev = insert;
		}
		insert.prev = base;
		insert.next = base.next;
		base.next = insert;
	}

	public void appendAsm(Asm asm) {
		asms.add(asm);
	}

	public List<Asm> getAsms() {
		return asms;
	}
}
