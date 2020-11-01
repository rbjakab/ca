package hu.bme.mit.ca.bmc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.Collections;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public final class BoundedModelChecker implements SafetyChecker {

	private final CFA cfa;
	private final int bound;
	private final int timeout;

	private BoundedModelChecker(final CFA cfa, final int bound, final int timeout) {
		checkArgument(bound >= 0);
		checkArgument(timeout >= 0);

		this.cfa = checkNotNull(cfa);
		this.bound = bound;
		this.timeout = timeout;
	}

	public static BoundedModelChecker create(final CFA cfa, final int bound, final int timeout) {
		return new BoundedModelChecker(cfa, bound, timeout);
	}

	@Override
	public SafetyResult check() {
		final Stopwatch stopwatch = Stopwatch.createStarted();

		while (stopwatch.elapsed(TimeUnit.SECONDS) < timeout) {
			int actLevel = 0;

			Vector<PathVertex> path = new Vector<>();
			int pathIndex = 0;

			CFA.Loc actLoc = cfa.getInitLoc();
			Queue<PathVertex> queue = new LinkedList<>();

			queue.add(new PathVertex(pathIndex, pathIndex, actLoc, null));
			path.add(new PathVertex(pathIndex, pathIndex, actLoc, null));

			pathIndex++;

			while(queue.size() != 0 && actLevel < bound) {
				PathVertex actPV = queue.remove();
				actLevel = getEdgePath(path).size();

				for (CFA.Edge edge : actPV.loc.getOutEdges()) {
					CFA.Loc nextLoc = edge.getTarget();

					PathVertex nextPV = new PathVertex(pathIndex, actPV.key, nextLoc, edge);
					pathIndex++;

					queue.add(nextPV);
					path.add(nextPV);

					if (nextLoc == cfa.getErrorLoc()) {
						List<Stmt> stmts = getStmtList(getEdgePath(path));
						Collection<Expr<BoolType>> exprs = StmtToExprTransformer.unfold(stmts);

						Solver solver = Z3SolverFactory.getInstace().createSolver();

						solver.push();
						solver.add(exprs);
						solver.check();

						if (solver.getStatus().isSat()) {
							System.out.println("UNSAFE -> level: " + actLevel + " bound: " + bound);
							return SafetyResult.UNSAFE;
						}

						solver.pop();
					}
				}
			}

			if (actLevel < bound) {
				System.out.println("SAFE -> level: " + actLevel + " bound: " + bound);
				return SafetyResult.SAFE;
			} else {
				System.out.println("UNKNOWN -> level: " + actLevel + " bound: " + bound);
				return SafetyResult.UNKNOWN;
			}

		}

		stopwatch.stop();

		return SafetyResult.TIMEOUT;
	}

	private List<CFA.Edge> getEdgePath(Vector<PathVertex> path) {
		List<CFA.Edge> edgeList = new ArrayList<>();
		PathVertex actPV = path.lastElement();

		while (actPV.key != 0) {
			edgeList.add(actPV.parentEdge);
			actPV = getParentVertex(path, actPV.parentKey);
		}

		return reverseList(edgeList);
	}

	private PathVertex getParentVertex(Vector<PathVertex> path, int key) {
		for (int i = 0; i < path.size(); i++) {
			if (path.get(i).key == key) {
				return path.get(i);
			}
		}
		return null;
	}

	private List<Stmt> getStmtList(List<CFA.Edge> edgePath) {
		List<Stmt> stmtList = new ArrayList<>();

		for (int i = 0; i < edgePath.size(); i++) {
			stmtList.add(edgePath.get(i).getStmt());
		}

		return stmtList;
	}

	private List<CFA.Edge> reverseList(List<CFA.Edge> edgeList) {
		List<CFA.Edge> reversedEdgeList = new ArrayList<>();

		for (int i = edgeList.size() - 1; i >= 0; i--) {
			reversedEdgeList.add(edgeList.get(i));
		}

		return reversedEdgeList;
	}
}
