package submit_a1;

import java.util.ArrayList;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PrimType;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootField;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

class DS {
	HashMap<String, HashSet<Integer>> rho;
	HashMap<Integer, HashMap<String, HashSet<Integer>>> sigma;

	public DS() {
		rho = new HashMap<String, HashSet<Integer>>();
		sigma = new HashMap<Integer, HashMap<String, HashSet<Integer>>>();

	}

	public DS(Chain<Local> vars) {
		rho = new HashMap<String, HashSet<Integer>>();
		sigma = new HashMap<Integer, HashMap<String, HashSet<Integer>>>();

		for (Local var : vars) {
			if (var.getType() instanceof RefLikeType) {
				rho.put(var.toString(), new HashSet<Integer>());
			}
		}

	}

	public static boolean isIntersect(HashSet<Integer> m, HashSet<Integer> n) {
		if (m == null || n == null)
			return false;

		if (m.contains(-1) || n.contains(-1))
			return true;

		HashSet<Integer> check = new HashSet<>();
		if (m.size() != 0)
			check.addAll(m);

		check.retainAll(n);

		if (check.size() != 0)
			return true;
		else
			return false;
	}

	public DS copy() {
		DS obj = new DS();
		obj.rho.putAll(rho);
		obj.sigma.putAll(sigma);

		return obj;

	}

	public static DS meetOpeation(DS m, DS n) {

		// merging stacks

		DS obj = new DS();

		HashSet<String> unique = new HashSet<String>();
		unique.addAll(m.rho.keySet());
		unique.addAll(n.rho.keySet());

		for (String s : unique) {
			if (m.rho.containsKey(s) && n.rho.containsKey(s))
				obj.rho.put(s, find_union_sets(m.rho.get(s), n.rho.get(s)));
			else if (m.rho.containsKey(s))
				obj.rho.put(s, m.rho.get(s));
			else
				obj.rho.put(s, n.rho.get(s));
		}

		// merging heaps

		HashSet<Integer> unique_keys = new HashSet<Integer>();
		unique_keys.addAll(m.sigma.keySet());
		unique_keys.addAll(n.sigma.keySet());

		for (Integer each : unique_keys) {

			if (m.sigma.containsKey(each) && n.sigma.containsKey(each)) {

				HashMap<String, HashSet<Integer>> temp_1 = new HashMap<>();

				temp_1.putAll(m.sigma.get(each));

				HashMap<String, HashSet<Integer>> temp_2 = new HashMap<>();

				temp_2.putAll(m.sigma.get(each));

				for (String s : temp_2.keySet()) {
					if (temp_1.containsKey(s)) {
						HashSet<Integer> total = find_union_sets(temp_1.get(s), temp_2.get(s));
						temp_1.put(s, total);
					} else
						temp_1.put(s, temp_2.get(s));

				}

				obj.sigma.put(each, temp_1);

			} else if (m.sigma.containsKey(each)) {
				HashMap<String, HashSet<Integer>> temp = new HashMap<>();
				temp.putAll(m.sigma.get(each));
				obj.sigma.put(each, temp);

			} else {
				HashMap<String, HashSet<Integer>> temp = new HashMap<>();

				temp.putAll(n.sigma.get(each));
//                obj.get(each).put(temp); 
				obj.sigma.put(each, temp);
			}
		}

		return obj;

	}

	public static HashSet<Integer> find_union_sets(HashSet<Integer> a, HashSet<Integer> b) {
		HashSet<Integer> obj = new HashSet<Integer>();
		obj.addAll(a);
		obj.addAll(b);
		return obj;
	}

	public static boolean isEquals(DS m, DS n) {
		if (m == n)
			return true;

		if (m.rho.equals(n.rho) == false)
			return false;

		if (m.sigma.equals(n.sigma) == false)
			return false;

		return true;

	}

}

class NewObjects {
	static HashMap<Unit, Integer> map = new HashMap<>();
	static int counter = 0;

}

public class AliasAnalysis extends BodyTransformer {

	public DS workListIterate(Body arg0) {

		UnitGraph cfg = new BriefUnitGraph(arg0);

		ArrayList<Unit> units = new ArrayList<>();

		for (Unit u : arg0.getUnits())
			units.add(u);

//		@SuppressWarnings("unchecked")
		NewObjects.map.clear();
		NewObjects.counter = 0;

		HashMap<Unit, DS> track = new HashMap<>();
		HashSet<Unit> worklist = new HashSet<>();

		Unit retUnit = null;

		Chain<Local> vars = arg0.getLocals();

		for (Unit unit : units) {

			track.put(unit, new DS(vars));
			worklist.add(unit);

			if (cfg.getSuccsOf(unit).size() == 0)
				retUnit = unit;
		}

		while (true) {

			if (worklist.size() == 0)
				break;

			Unit current = worklist.iterator().next();
			worklist.remove(current);
			DS t = track.get(current);

			DS total_effect = new DS(vars);

			for (Unit pred : cfg.getPredsOf(current)) {
				DS pred_in = flowFunction(track.get(pred), pred, track);

				total_effect = DS.meetOpeation(total_effect, pred_in);
			}

			if (DS.isEquals(total_effect, track.get(current)) == false) {

				track.put(current, total_effect);
				worklist.addAll(cfg.getSuccsOf(current));
			}

		}
		return track.get(retUnit);

	}

	@SuppressWarnings("unchecked")
	public DS flowFunction(DS in, Unit unit, HashMap<Unit, DS> track) {

		Stmt s = (Stmt) unit;

		DS out = in.copy();

		if (s instanceof DefinitionStmt == false && s instanceof InvokeStmt)
			return out;

		if (s instanceof InvokeStmt) {
			if (s.getInvokeExpr() instanceof SpecialInvokeExpr)
				return out;
			else {
				
				InvokeStmt is = (InvokeStmt) s;
				InvokeExpr ir = is.getInvokeExpr();
				List<Value> arguments = ir.getArgs();
				VirtualInvokeExpr v_ir = (VirtualInvokeExpr) ir;
				String a = v_ir.getBase().toString();

				// TODO
			}

			return out;

		}
		DefinitionStmt ds;
		try {
			ds = (DefinitionStmt) s;
		} catch (Exception e) {
//			System.out.println("casting exception");
			return out;
		}

		Value lhs = ds.getLeftOp();
		Value rhs = ds.getRightOp();
//		System.out.println("parent " + unit);

		if ((lhs.getType() instanceof PrimType) || (rhs.getType() instanceof PrimType))
			return out;

		if (lhs.getType() instanceof RefLikeType && rhs.getType() instanceof RefLikeType && rhs instanceof NewExpr) {
			// new statement

			out.rho.put(lhs.toString(), new HashSet<Integer>());

			if (NewObjects.map.get(unit) == null) {
				NewObjects.map.put(unit, NewObjects.counter);

				RefType rt = (RefType) rhs.getType();
				SootClass className = rt.getSootClass();

				HashMap<String, HashSet<Integer>> map = new HashMap<String, HashSet<Integer>>();

				Chain<SootField> fields = className.getFields();

				for (SootField each : fields) {
					HashSet<Integer> temp = new HashSet<Integer>();
					map.put(each.toString(), temp);

				}
				out.sigma.put(NewObjects.counter, map);

				NewObjects.counter += 1;

			}

			out.rho.get(lhs.toString()).add(NewObjects.map.get(unit));
			return out;

		}

		else if (lhs.getType() instanceof RefLikeType && rhs.getType() instanceof RefLikeType && lhs instanceof Local
				&& rhs instanceof Local) {

			// copy statement

			HashSet<Integer> copy = new HashSet<Integer>();
//			track.get(unit).print();

			if (in.rho.get(rhs.toString()) != null)
				copy.addAll(in.rho.get(rhs.toString()));

			out.rho.put(lhs.toString(), copy);

		}

		else if (lhs.getType() instanceof RefLikeType && rhs.getType() instanceof RefLikeType
				&& rhs instanceof InstanceFieldRef) {

			// Load statement x=y.f

			InstanceFieldRef n = (InstanceFieldRef) rhs;

			SootField field = n.getField();
			Value val = n.getBase();

			HashSet<Integer> temp = in.rho.get(val.toString());

			HashSet<Integer> o = new HashSet<Integer>();

			for (Integer item : temp) {

				o.addAll(in.sigma.get(item).get(field.toString()));

			}
			out.rho.put(lhs.toString(), o);

			return out;

		}

		else if (lhs.getType() instanceof RefLikeType && rhs.getType() instanceof RefLikeType
				&& lhs instanceof InstanceFieldRef) {

			// Store statement x.f=y

			InstanceFieldRef ne = (InstanceFieldRef) lhs;

			SootField field = ne.getField();
			Value base = ne.getBase();

			HashSet<Integer> n = in.rho.get(base.toString());

			if (n != null && n.size() == 1) {

				// strong update
				Integer a = -1;

				for (Integer each : n)
					a = each;

				out.sigma.get(a).get(field.toString()).clear();
				out.sigma.get(a).get(field.toString()).addAll(in.rho.get(rhs.toString()));

			} else {

				// weak update
//				System.out.println(lhs.toString());
				for (Integer a : in.rho.get(base.toString())) {

					out.sigma.get(a).get(field.toString()).addAll(in.rho.get(rhs.toString()));

				}

			}

		} else if (ds.containsInvokeExpr()) {

			InvokeExpr ir = ds.getInvokeExpr();
			VirtualInvokeExpr v_ir = (VirtualInvokeExpr) ir;
			Value b = v_ir.getBase();

			Value a = lhs;
			List<Value> arguments = ir.getArgs();
			

			// update lhs to be -1

			out.rho.get(lhs.toString()).clear();
			out.rho.get(lhs.toString()).add(-1);

			// update heaps for object calling and also for arguments

			HashSet<Integer> temp = new HashSet<Integer>();
			temp.addAll(out.rho.get(b.toString()));

			for (Integer each : temp) {

				HashMap<String, HashSet<Integer>> li = new HashMap<String, HashSet<Integer>>();
				li.putAll(out.sigma.get(each));

				for (Map.Entry<String, HashSet<Integer>> fieldSet : li.entrySet()) {
					li.get(fieldSet.getKey()).clear();
					li.get(fieldSet.getKey()).add(-1);

				}

				out.sigma.put(each, li);

			}
			return out;

		}

		return out;

	}

	@Override
	protected synchronized void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {

		String methodName = arg0.getMethod().getName();

		if (methodName == "<init>")
			return;

//		System.out.println(methodName);

		String className = arg0.getMethod().getDeclaringClass().toString();

		UnitGraph cfg = new BriefUnitGraph(arg0);
//		System.out.println("Method body: - " + arg0);

		DS output = workListIterate(arg0);

		for (int i = 0; i < A1.queryList.size(); i++) {

			String queryClass = A1.queryList.get(i).getClassName();
			String queryMethod = A1.queryList.get(i).getMethodName();
			String leftVar = A1.queryList.get(i).getLeftVar();
			String rightVar = A1.queryList.get(i).getRightVar();

			if (queryClass.equals(className) & queryMethod.equals(methodName)) {
				if (DS.isIntersect(output.rho.get(leftVar), output.rho.get(rightVar)))
					A1.answers[i] = "Yes";

				else
					A1.answers[i] = "No";

			}
		}
	}

}