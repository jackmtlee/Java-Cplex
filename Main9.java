import java.util.ArrayList;
import java.util.List;

import ilog.concert.IloConstraint;
import ilog.concert.IloException;
import ilog.concert.IloIntVar;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloLinearNumExprIterator;
import ilog.concert.IloNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import ilog.concert.IloObjective;
import ilog.concert.IloRange;
import ilog.cplex.IloCplex;
/**
 * 
 * @author Administrator
 * 主问题目标函数不变， 约束变了（一点点增加)； 
 * 子问题约束不变，但目标函数每一轮都变（主问题中固定的变量进行的调整）
 */
public class Main9 
{
	final int MAX = 5;
	int[][] unitShippingCost = {{8,21,42,12,37},
			{21,10,31,24,40},
			{42,31,4,14,32},
			{12,24,14,7,12},
			{37,40,32,12,10}};
	int[] demand = {30,40,50,35,40};                    //  d
	int[] maxCapacity = {80,80,80,80,80};               
	int[] fixedCost = {1000, 1500, 1700, 1400, 1200};   // f
	int[] variableCost = {20, 17, 13, 25, 33};          //  v
	//  存储所有的约束
	List<IloConstraint> constraints = new ArrayList<IloConstraint>();
	
    double UB,LB;
    final double FUZZ = 1e-7;
    IloCplex master = null;
    IloCplex subProblem = null;
    IloNumVar subcost = null;
    
    IloObjective subobj = null;   // 记录子问题目标函数
    //  对偶子问题中的决策变量
    IloNumVar[] uVars;
    IloNumVar[] vVars;
    IloNumVar[] wVars;
    //  主问题中的决策变量
    IloNumVar[] yVars = new IloNumVar[MAX];
    IloNumVar[] zVars = new IloNumVar[MAX];
    //  主问题中固定，子问题中变化的y,z的值
    int[] y1 = new int[MAX];
    int[] z1 = new int[MAX];
	// benders算法求解过程
	public void benders_solve() throws Exception 
	{
		UB = Double.MAX_VALUE;
		LB = Double.MIN_VALUE;
		while (UB - LB > FUZZ) 
		{	
			// 根据松弛的主问题中的 变量y值重置子问题目标函数. 
			IloLinearNumExpr subobj_expr0 = subProblem.linearNumExpr();		
			
			for(int i = 0; i < MAX; ++i)
			{
				subobj_expr0.addTerm(demand[i], uVars[i]);
				subobj_expr0.addTerm(-z1[i], vVars[i]);
				subobj_expr0.addTerm(-maxCapacity[i] * y1[i], wVars[i]);
			}	
			
			subobj.setExpr(subobj_expr0);      // 重置子问题目标函数 ，因为y的值变了。 obj: (b-By)u
			subProblem.solve();                // 但子问题约束并不需要重置， s.t.  Au <= c
			                                   //  这里只有u是决策变量，剩下都是常数，y是每轮调整的
			IloCplex.Status status = subProblem.getStatus();			
			// 判断子问题的求解状态。 子问题无界，加入一条极射线. 对偶问题无界，说明原问题无解(无可行解)
			if (status == IloCplex.Status.Unbounded)  // 这里肯定能取到极射线， 也能取到极点吧？？？
			{
				//  既然无界， 怎么还能有值呢？？？？？？？？？ 不是应该是无穷吗？？？
				System.err.println("~~~~~~~~~~unbounded, the value is " + subProblem.getObjValue());
				IloLinearNumExpr ray = subProblem.getRay();   //  极射线从subproblem的可行域中来, 此可行域不变吧？？？
				
				System.out.println("getRay returned " + ray.toString());
				IloLinearNumExprIterator it = ray.linearIterator();  
				double[] uCoef = new double[MAX];    //  极射线中x的系数, 即对偶子问题中的决策变量u的系数	
				double[] vCoef = new double[MAX]; 
				double[] wCoef = new double[MAX]; 
				
//				double[] uCoef1 = new double[MAX];    //  极点中的系数， 肯定应该有极点吧。
//				double[] vCoef1 = new double[MAX]; 
//				double[] wCoef1 = new double[MAX]; 
//				uCoef1 = subProblem.getValues(uVars);
//				vCoef1 = subProblem.getValues(vVars);
//				wCoef1 = subProblem.getValues(wVars);
//				System.err.println("extreme points in unbounded sceario " + uCoef1[0]);
//				System.err.println("extreme points in unbounded sceario " + vCoef1[0]);
//				System.err.println("extreme points in unbounded sceario " + wCoef1[0]);
				
				while (it.hasNext()) 
				{
					IloNumVar var = it.nextNumVar();       // 这个应该是返回射线中，决策变量那一项。
					boolean varFound = false;					
					//  需求约束变量
					for (int i = 0; i < MAX && !varFound; i++) {
						if (var.equals(uVars[i]))
						{         //  表示的确是这一项决策变量，这里的equals()方法并未改写。如何比较两个变量呢？？
							uCoef[i] = it.getValue();
							varFound = true;
						}
						if(var.equals(vVars[i]))
						{
							vCoef[i] = it.getValue();
							varFound = true;
						}
						if(var.equals(wVars[i]))
						{
							wCoef[i] = it.getValue();
							varFound = true;
						}
					}
				}		
				// 构造要添加到主问题的约束方程   也就是生成 的切平面。 约束方程的形式： (b-By)u <=0  ---->  bu <= yBu , 左边是一个标量， 右侧是线性表达式
				// 这个约束中只有y是变量（注意这个时候的y成为变量了，因为是在主问题中。在子问题中的y是常量)。
				IloLinearNumExpr expr1 = master.linearNumExpr();
				double rightHandSide = 0;
                for(int i = 0; i < MAX; ++i)
                {
                	expr1.addTerm(-vCoef[i], zVars[i]);
                	expr1.addTerm(-maxCapacity[i] * wCoef[i], yVars[i]);
                	rightHandSide += demand[i] * uCoef[i];
                }
				IloConstraint extremeRayConstraint = master.addCut((IloRange)master.le(expr1, -rightHandSide));
				// 添加约束方程到主问题中， 这个切平面要加入到主问题中
				System.out.println("\n>>> Adding feasibility cut: " + extremeRayConstraint + "\n");		
			}
			//  extreme points are extreme rays are from feasible region
			//  找一个极点。 这里肯定能找到极点 ， 也有可能找到极射线 polyhedron（不保证能找到 polytope）
			else if (status == IloCplex.Status.Optimal)
			{			
//				IloLinearNumExpr ray = subProblem.getRay();     //  
//				System.err.println("get ray from optimal senario " + ray.toString());  //  若无法执行， 证明没有极射线。
				System.err.println(isExtremeRayExisted(subProblem)); //  true if there exist extreme rays, false otherwise
				// 子问题有解，则最优解即一个极值点			
				double[] uCoef = new double[MAX];    //  极射线中x的系数, 即对偶子问题中的决策变量u的系数	
				double[] vCoef = new double[MAX]; 
				double[] wCoef = new double[MAX]; 
				//  得到极点的(系数),  注意和极射线情况下获取系数的区别
				uCoef = subProblem.getValues(uVars);
				vCoef = subProblem.getValues(vVars);
				wCoef = subProblem.getValues(wVars);
				
				double rightHandSide = 0; 		
				double[] temp = new double[MAX];				
				// 构造要添加到主问题的约束方程
				IloLinearNumExpr expr1 = master.linearNumExpr();
				for(int i = 0; i < MAX; ++i)
				{
                	expr1.addTerm(-vCoef[i], zVars[i]);
                	expr1.addTerm(-maxCapacity[i] * wCoef[i], yVars[i]);
                	rightHandSide += demand[i] * uCoef[i];
				}

				expr1.addTerm(-1, subcost);	
				// 添加约束方程到主问题中  (b - By)u <= subcost    ------>   yBu + subcost >= bu
				IloConstraint extremePointConstraint = master.addCut((IloRange)master.le(expr1, -rightHandSide));

				double masterProblemValue = 0;	   			
				for(int i = 0; i < MAX; ++i)
				{
					masterProblemValue += fixedCost[i] * y1[i];
					masterProblemValue += variableCost[i] * z1[i];
				}
				//  UB = min{UB, fTY + (b - By)u }
				UB = Math.min(UB, masterProblemValue + subProblem.getObjValue());      // 主问题为最小化， 更新上界
				System.err.println("UB~~~~~~~~~~~~~" + UB);
				System.out.println("\n>>> Adding optimality cut: " + extremePointConstraint + "\n");			
			} 
			else { // unexpected status -- report but do nothing
				   // 出现不希望出现的状态，非法
				System.err.println("\n!!! Unexpected subproblem solution status: " + status + "\n");
			}
			
            //  重新解主问题（加入新的约束后,)， 更新下界,  MP一定有界。 否则整个问题无解了。
			master.solve();      //  解主问题，更新下界  ； 若原问题是极大化问题，则更新上界
			LB = master.getObjValue();
			
            System.err.println("LB~~~~~~~~~~~~~" + LB);
			// 获得主问题中的变量y值， 在求解的过程中，实际上是把y给松弛掉了。这样得到的就不是整数了， 故每轮循环后， 要重新设定y的值。
			// 事实上，主问题中只有y一组决策变量， 把y值求出后强行转换成整数，然后继续迭代下一轮。
			for (int i = 0; i < MAX; i++) 
			{
				double yy = master.getValue(yVars[i]);
				y1[i] = (int)Math.round(yy);      //  将constantY进行四舍五入
				double zz = master.getValue(zVars[i]);
				z1[i] = (int)Math.round(zz);
			} // end for
		}//  end while 结束整个Benders       
	}//  end benders_solve()
	
	// 建立主问题和子问题的cplex模型
	public void bendersModel() throws IloException {
		subProblem = new IloCplex();// 子问题
		master = new IloCplex(); // 主问题
		// 参数初始化
		// 参数约束                                                                                                                                                                        变量表达式的名字就叫做subcost
		subcost = master.numVar(0.0, Double.MAX_VALUE, IloNumVarType.Float, "subcost");  //  子问题的表达式（参数）	
		//  这里的y,z 为什么一定要是整数呢？ 小数为什么不行？
		for(int i = 0; i < MAX; ++i)
		{
			yVars[i] = subProblem.numVar(0, 1, IloNumVarType.Int, "Y_" + i);
			zVars[i] = subProblem.numVar(0, maxCapacity[i], IloNumVarType.Int, "Z_" + i);
		}  //  初始化主问题决策变量

		// 主问题表达式
		IloNumExpr expr0 = master.numExpr();
		for(int i = 0; i < MAX; ++i)
		{
		   expr0 = master.sum(expr0, master.prod(fixedCost[i], yVars[i])); 
		   expr0 = master.sum(expr0, master.prod(variableCost[i], zVars[i]));
		}
		System.out.println("主问题表达式：" + expr0);
		//  整个问题的目标函数： 子问题表达式subcost + 主问题表达式
		master.addMinimize(master.sum(subcost, expr0), "TotalCost");   //  最小化问题，循环中更新上界； 若是最大化问题，则循环中更新下界

        //  以下是子问题构造
        uVars = new IloNumVar[MAX];
		vVars = new IloNumVar[MAX];
		wVars = new IloNumVar[MAX];
		// 子问题目标函数
		IloLinearNumExpr obj = subProblem.linearNumExpr();

		for(int i = 0; i < MAX; ++i)
		{
			uVars[i] = subProblem.numVar(0, Double.MAX_VALUE, "U_" + i);
//			uVars[i] = subProblem.numVar(0, Integer.MAX_VALUE, "U_" + i);
			vVars[i] = subProblem.numVar(0, Double.MAX_VALUE, "V_" + i);
			wVars[i] = subProblem.numVar(0, Double.MAX_VALUE, "W_" + i);
			obj.addTerm(demand[i], uVars[i]);
			obj.addTerm(-z1[i], vVars[i]);
			obj.addTerm(-maxCapacity[i] * y1[i], wVars[i]);
		}
		subobj = subProblem.addMaximize(obj, "dualSubCost");		

		// 子问题约束方程， 每一次循环都添加一个约束	(这个地方可能有问题， 分不清i, j)
		for(int i = 0; i < MAX; ++i)
		{
		    for(int j = 0; j < MAX; ++j)
		    {
			    IloLinearNumExpr expression = subProblem.linearNumExpr();
		    	expression.addTerm(1, uVars[j]);
		    	expression.addTerm(-1, vVars[i]);
		    	expression.addTerm(-1, wVars[i]);
			    constraints.add(subProblem.addLe(expression, unitShippingCost[i][j], "C_" + i + "_" +j));
		    }
		}		
		// turn off the presolver for the main model。 这里的参数选取特别的重要。  参数选取直接影响最终结果。
		subProblem.setParam(IloCplex.BooleanParam.PreInd, false);
		subProblem.setParam(IloCplex.Param.RootAlgorithm, IloCplex.Algorithm.Primal);
	}   
	//  注意cplex中每次只能得到一个极点或极射线， 到底得到哪一个，不受我们控制。
	private void outputExtremePointsOrRays(double[] values)   // 极点与极射线完全来自于可行域中， 故，若可行域不变，则它们也不变。
	{
		int size = values.length;
		for(int i = 0; i< size; ++i)
		{
			System.out.print(values[i] + ",");
		}
		System.out.println("");
	}
    //  to judge if there exist extrem rays in feaisble region
	//   extreme rays only exist in polyhedral but polytope.
	private boolean isExtremeRayExisted(IloCplex subProblem)
	{
		try
		{
			IloLinearNumExpr ray = subProblem.getRay();
			return true;
		}
		catch (Exception e) { return false;	}
	}
	
	void bendersDecompostion() throws Exception
	{
		bendersModel();
		benders_solve();
		if(master.getStatus() == IloCplex.Status.Optimal)
			System.out.println("the objective value is " + master.getObjValue());
		else System.out.println("error status");
	}
	void setYZ()    //  先把y,z固定，然后在benders中动态调整
	{
		for(int i = 0; i < MAX; ++i)
		{
			y1[i] = 1;
			z1[i] = 1;
		}
	}
	public static void main(String[] args) throws Exception
	{  new Main9().bendersDecompostion();	}
}