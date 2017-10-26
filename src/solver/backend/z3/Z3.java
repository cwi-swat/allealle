package solver.backend.z3;

public class Z3 {
//	private Context ctx;
//	
//	private final TypeReifier tr;
//	private final TypeFactory tf;
//	
//	private Set<BoolExpr> rootFormulas;
//	private Set<Handle> optimizationCommands;
//	
//	private Solver solver;
//	private Optimize optimizer;
//	
//	private Map<Type, Function<IConstructor, Expr>> formConversion;
//	private Map<Type, Function<IConstructor, Handle>> optConversion;
//	
//	public Z3(IValueFactory vf) {
//		this.tr = new TypeReifier(vf);
//		this.tf = TypeFactory.getInstance();
//		
//		this.rootFormulas = new HashSet<>();
//		this.optimizationCommands = new HashSet<>();
//	}
//	
//	public void init(IValue formType, IValue commandType, IEvaluatorContext ec) {
//		reset();
//		
//		formConversion = buildFormulaConversionMap(formType, ec);
//		optConversion = buildCommandConversionMap(commandType, ec);
//	}
//	
//	public void reset() {
//		rootFormulas.clear();
//		optimizationCommands.clear();
//		
//		Map<String,String> cfg = new HashMap<>();
//		cfg.put("model", "true");
//		ctx = new Context(cfg);
//		
//		optimizer = ctx.mkOptimize();
//	}
//	
//	public Map<Type, Function<IConstructor, Expr>> buildFormulaConversionMap(IValue formType, IEvaluatorContext ec) {
//		TypeStore store = new TypeStore(RascalValueFactory.getStore());
//		tr.valueToType((IConstructor) formType, store);
//
//		Type formula = store.lookupAbstractDataType("Formula");
//		
//		Map<Type, Function<IConstructor, Expr>> lookup = new HashMap<>();
//		
//		// core formulas
//		lookup.put(store.lookupConstructor(formula, "true", tf.tupleEmpty()), (t) -> ctx.mkTrue());
//		lookup.put(store.lookupConstructor(formula, "false", tf.tupleEmpty()), (f) -> ctx.mkFalse());
//		lookup.put(store.lookupConstructor(formula, "var", tf.tupleType(tf.stringType())), (v) -> ctx.mkBoolConst(((IString)v.get(0)).getValue()));
//		lookup.put(store.lookupConstructor(formula, "not", tf.tupleType(formula)), (n) -> ctx.mkNot((BoolExpr) convert(n.get(0), ec)));
//		lookup.put(store.lookupConstructor(formula, "and", tf.tupleType(tf.setType(formula))), (and) -> ctx.mkAnd(convertChildren((ISet)and.get(0), ec).toArray(new BoolExpr[0])));
//		lookup.put(store.lookupConstructor(formula, "or", tf.tupleType(tf.setType(formula))), (or) -> ctx.mkOr(convertChildren((ISet)or.get(0), ec).toArray(new BoolExpr[0])));
//		lookup.put(store.lookupConstructor(formula, "ite", tf.tupleType(formula, formula, formula)), (ite) -> ctx.mkITE((BoolExpr)convert(ite.get(0),ec), convert(ite.get(1),ec), convert(ite.get(2),ec)));
//
//		// int formulas
//		lookup.put(store.lookupConstructor(formula, "int", tf.tupleType(tf.integerType())), (i) -> ctx.mkInt(((IInteger)i.get(0)).intValue())); 
//		lookup.put(store.lookupConstructor(formula, "intVar", tf.tupleType(tf.stringType())), (v) -> ctx.mkIntConst(((IString)v.get(0)).getValue()));
//		lookup.put(store.lookupConstructor(formula, "neg", tf.tupleType(formula)), (f) -> ctx.mkUnaryMinus((ArithExpr) convert(f.get(0),ec))); 
//		lookup.put(store.lookupConstructor(formula, "addition", tf.tupleType(tf.listType(formula))), (terms) -> ctx.mkAdd(convertChildren((IList)terms.get(0),ec).toArray(new ArithExpr[0]))); 
//		lookup.put(store.lookupConstructor(formula, "multiplication", tf.tupleType(tf.listType(formula))), (terms) -> ctx.mkAdd(convertChildren((IList)terms.get(0),ec).toArray(new ArithExpr[0]))); 
//		lookup.put(store.lookupConstructor(formula, "modulo", tf.tupleType(formula, formula)), (mod) -> ctx.mkMod((IntExpr)convert(mod.get(0),ec), (IntExpr)convert(mod.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "division", tf.tupleType(formula, formula)), (div) -> ctx.mkDiv((ArithExpr)convert(div.get(0),ec), (ArithExpr)convert(div.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "distinct", tf.tupleType(tf.listType(formula))), (terms) -> ctx.mkDistinct(convertChildren((IList)terms.get(0),ec).toArray(new Expr[0]))); 
//
//		lookup.put(store.lookupConstructor(formula, "lt", tf.tupleType(formula, formula)), (lt) -> ctx.mkLt((ArithExpr)convert(lt.get(0),ec), (ArithExpr)convert(lt.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "lte", tf.tupleType(formula, formula)), (lte) -> ctx.mkLe((ArithExpr)convert(lte.get(0),ec), (ArithExpr)convert(lte.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "gt", tf.tupleType(formula, formula)), (gt) -> ctx.mkGt((ArithExpr)convert(gt.get(0),ec), (ArithExpr)convert(gt.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "gte", tf.tupleType(formula, formula)), (gte) -> ctx.mkGe((ArithExpr)convert(gte.get(0),ec), (ArithExpr)convert(gte.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "lt", tf.tupleType(formula, formula)), (lt) -> ctx.mkLt((ArithExpr)convert(lt.get(0),ec), (ArithExpr)convert(lt.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "equal", tf.tupleType(formula, formula)), (eq) -> ctx.mkEq(convert(eq.get(0),ec), convert(eq.get(1),ec))); 
//		lookup.put(store.lookupConstructor(formula, "inequal", tf.tupleType(formula, formula)), (eq) -> ctx.mkNot(ctx.mkEq(convert(eq.get(0),ec), convert(eq.get(1),ec)))); 
//		
//		return lookup;
//	}
//
//	public Map<Type, Function<IConstructor, Handle>> buildCommandConversionMap(IValue comType, IEvaluatorContext ec) {
//		TypeStore store = new TypeStore(RascalValueFactory.getStore());
//		tr.valueToType((IConstructor) comType, store);
//
//		Type command = store.lookupAbstractDataType("Command");
//		Type formula= store.lookupAbstractDataType("Formula");
//		
//		Map<Type, Function<IConstructor, Handle>> lookup = new HashMap<>();
//		
//		lookup.put(store.lookupConstructor(command, "maximize", tf.tupleType(formula)), (t) -> optimizer.MkMaximize((ArithExpr) convert(t.get(0), ec)));
//		lookup.put(store.lookupConstructor(command, "minimize", tf.tupleType(formula)), (t) -> optimizer.MkMinimize((ArithExpr) convert(t.get(0), ec)));
//		
//		return lookup;
//	}
//
//	
//	private Expr convert(IValue form, IEvaluatorContext ec) {
//		IConstructor formula = (IConstructor)form;
//		if (!formConversion.containsKey(formula.getConstructorType())) {
//			ec.getStdErr().println("No conversion function for '" + formula.getConstructorType() + "'");
//		}
//		
//		return formConversion.get(formula.getConstructorType()).apply(formula);
//	}
//	
//	private List<Expr> convertChildren(Iterable<IValue> formulas, IEvaluatorContext ec) {
//		List<Expr> childExprs = new ArrayList<>(); 
//		for (IValue elem: formulas) {
//			IConstructor elemForm = (IConstructor)elem;
//			childExprs.add(formConversion.get(elemForm.getConstructorType()).apply(elemForm));
//		}
//		
//		return childExprs;
//	}
//	
//	public void assertFormula(IConstructor formula, IEvaluatorContext ec) {
//		rootFormulas.add((BoolExpr)convert(formula, ec));
//	}
//	
//	public void addOptimizeCommand(IConstructor command, IEvaluatorContext ec) {
//		optimizationCommands.add(optConversion.get(command.getConstructorType()).apply(command));
//	}
//	
//	private boolean isOptimizationProblem() {
//		return !optimizationCommands.isEmpty();
//	}
//	
//	public void check(IEvaluatorContext ec) {
//		Status status;
//		if (isOptimizationProblem()) {
//			// its an optimization problem, use the optimizer
//			for (BoolExpr expr : rootFormulas) {
//				optimizer.Add(expr);
//			}
//			
//			status = optimizer.Check();
//		} else {
//			solver = ctx.mkSolver();
//			for (BoolExpr expr : rootFormulas) {
//				solver.add(expr);
//			}
//			
//			status = solver.check();
//		}
//		
//		ec.getStdOut().println(status);
//		
////		if (isOptimizationProblem()) {
////			ec.getStdOut().println(optimizer);
////		} else {
////			ec.getStdOut().println(solver);
////		}
//	}
}
