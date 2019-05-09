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
import tools.*;
/**
 *  max_index = 3;
c = [1,2,3];
f = [1,2,3];
A = [[2,3,1],[4,3,2],[5,6,2]];
B = [[3,4,6],[6,4,2],[1,4,7]];
b = [2.3, 4.6, 5.1];     
应用这个算法之前，必须手动分解模型，找出主问题， 子问题目标， 子问题约束
考虑，算法中哪些部分是通用部分（可以写成模板）， 哪一些是特殊部分。 
个人认为主要工作在于： 如何针对一个具体的模型，通过分解，确定其主问题，子问题目标与子问题约束
一个极为重要的问题： 如果子问题中存在整数变量的话，即混合整数规划，怎么办？？？ 若子问题为最优还好， 若无界的话，如何获得极射线？？？？？
 */
public class Main8
{
    final int MAX = 3;
    final int[] c = {1,2,3};
    final int[] f = {1,2,3};
    final int[][] A = {{2,3,1},{4,3,2},{5,6,2}};
    //final int[][] At = {{2,4,5},{3,3,6},{1,2,2}};
    int[][] At = Tool.getTransposeMatrix(A, MAX, MAX);
    final int[][] B = {{3,4,6},{6,4,2},{1,4,7}};  
    //final int[][] Bt = {{3,6,1},{4,4,4},{6,2,7}}; 
    int[][] Bt = Tool.getTransposeMatrix(B, MAX, MAX);
    final double[] b = {2.3, 4.6, 5.1};
    double UB,LB;
    IloCplex master = null;
    IloCplex subProblem = null;
    IloNumVar subcost = null;
    
    int[] constantY = new int[MAX];     //  给定的固定y值 
    double[] By = new double[MAX];         // 计算B*y
    double[] bMinusBy = new double[MAX];   //  计算b-B*y
    
    IloObjective subobj;// 记录子问题目标函数
    
    IloNumVar[] xDualVar;  //  x的对偶变量
    IloNumVar[] yVar;
    
    final double FUZZ = 1e-7;
    ArrayList<IloConstraint> constraints = new ArrayList<IloConstraint>();
    
    void bendersDecompostion() throws Exception
    {
		bendersModel();
		benders_solve();
		if(master.getStatus() == IloCplex.Status.Optimal)
		{
			System.out.println("the objective value is " + master.getObjValue());
		}
		else System.out.println("error status");
    }
	
	void initializeY()   //  给y一个初值（固定）, 只调用一次，以后将动态调整
	{  
		for(int i = 0; i < MAX; ++i)   constantY[i] = 1;
	}
	void compute_By()
	{
		for(int i = 0; i < MAX; ++i) By[i] = 0;   // 先初始化为0
		for(int i = 0; i < MAX; ++i)
			for(int j = 0; j < MAX; ++j)
				By[i] += B[i][j] * constantY[j];
	}
	void compute_bMinusBy()
	{
		for(int i = 0; i < MAX; ++i)
			bMinusBy[i] = b[i] - By[i];
	}
	// benders算法求解过程
	public void benders_solve() throws Exception 
	{
		UB = Double.MAX_VALUE;
		LB = Double.MIN_VALUE;
		while (UB - LB > FUZZ) 
		{
			// 根据松弛的主问题中的 变量y值重置子问题目标函数. 
			//  因为y的值每一轮都会调整（四舍五入)， 所以相关的矩阵也变了，必须重新计算
			compute_By();
			compute_bMinusBy();
			//  
			IloLinearNumExpr subobj_expr0 = subProblem.linearNumExpr();		
			
			for(int i = 0; i < MAX; ++i)
				subobj_expr0.addTerm(bMinusBy[i], xDualVar[i]);		
			
			subobj.setExpr(subobj_expr0);      // 重置子问题目标函数 ，因为y的值变了。 obj: (b-By)u
			subProblem.solve();                // 但子问题约束并不需要重置， s.t.  Au <= c
			                                   //  这里只有u是决策变量，剩下都是常数，y是每轮调整的
			IloCplex.Status status = subProblem.getStatus();			
			// 判断子问题的求解状态。 子问题无界，加入一条极射线
			if (status == IloCplex.Status.Unbounded) 
			{
				// 获得射线// 获得子问题的一条极射线, 这里能得到哪一条射线呢？ 是否存在多条射线？？？
				IloLinearNumExpr ray = subProblem.getRay();   //  射线从subproblem中来
				
				System.out.println("getRay returned " + ray.toString());
				// 记录极射线的参数, 这个迭代器中的内容应该是IloLinearNumExpr.addTerm()中的参数，即多项式中的每一项。
				IloLinearNumExprIterator it = ray.linearIterator();  
				double[] xCoef = new double[MAX];    //  极射线中x的系数, 即对偶子问题中的决策变量u的系数			
				while (it.hasNext()) 
				{
					IloNumVar var = it.nextNumVar();       // 这个应该是返回射线中，决策变量那一项。
					boolean varFound = false;					
					//  需求约束变量
					for (int i = 0; i < MAX && !varFound; i++) {
						if (var.equals(xDualVar[i])) {         //  表示的确是这一项决策变量，这里的equals()方法并未改写。
							xCoef[i] = it.getValue();
							varFound = true;
						}
					}
				}		
				double rightHandSide = 0; 		
				double[] temp = new double[MAX];	
				
				// 构造要添加到主问题的约束方程   也就是生成 的切平面。 约束方程的形式： (b-By)u <=0  ---->  bu <= yBu , 左边是一个标量， 右侧是线性表达式
				// 这个约束中只有y是变量（注意这个时候的y成为变量了，因为是在主问题中。在子问题中的y是常量)。
				IloLinearNumExpr expr1 = master.linearNumExpr();
				for(int i = 0; i < MAX; ++i)
				{
					rightHandSide += b[i] * xCoef[i];
					temp[i] = 0;
					for(int j = 0; j < MAX; ++j)
					{
						temp[i] += Bt[i][j] * xCoef[j];
					}
				}
				for(int k = 0; k < MAX; ++k)
					expr1.addTerm(temp[k], yVar[k]);
				IloConstraint extremeRayConstraint = master.addCut((IloRange)master.ge(expr1, rightHandSide));
				// 添加约束方程到主问题中， 这个切平面要加入到主问题中
				System.out.println("\n>>> Adding feasibility cut: " + extremeRayConstraint + "\n");		
			}
			
			else if (status == IloCplex.Status.Optimal) //  找一个极点
			{			
				// 子问题有解，则最优解即一个极值点			
				double[] xCoef = new double[MAX];    //  极点中x的系数
				//  得到极点的(系数),  注意和极射线情况下获取系数的区别
				xCoef = subProblem.getValues(xDualVar);
				
				double rightHandSide = 0; 		
				double[] temp = new double[MAX];				
				// 构造要添加到主问题的约束方程
				IloLinearNumExpr expr1 = master.linearNumExpr();
				for(int i = 0; i < MAX; ++i)
				{
					rightHandSide += b[i] * xCoef[i];
					temp[i] = 0;
					for(int j = 0; j < MAX; ++j)
					{
						temp[i] += Bt[i][j] * xCoef[j];
					}
				}
				for(int k = 0; k < MAX; ++k)
					expr1.addTerm(temp[k], yVar[k]);
				expr1.addTerm(1, subcost);	
				// 添加约束方程到主问题中  (b - By)u <= subcost    ------>   yBu + subcost >= bu
				IloConstraint extremePointConstraint = master.addCut((IloRange)master.ge(expr1, rightHandSide));

				double fTY = 0;	   			
				for(int i = 0; i < MAX; ++i)
					fTY += f[i] * constantY[i];
				//  UB = min{UB, fTY + (b - By)u }
				UB = Math.min(UB, fTY + subProblem.getObjValue());      // 主问题为最小化， 更新上界
				System.out.println("\n>>> Adding optimality cut: " + extremePointConstraint + "\n");			
			} 
			else { // unexpected status -- report but do nothing
				   // 出现不希望出现的状态，非法
				System.err.println("\n!!! Unexpected subproblem solution status: " + status + "\n");
			}
            //  重新解主问题（加入新的约束后,)， 更新下界
			master.solve();      //  解主问题，更新下界  ； 若原问题是极大化问题，则更新上界
			LB = master.getObjValue();

			// 获得主问题中的变量y值， 在求解的过程中，实际上是把y给松弛掉了。这样得到的就不是整数了， 故每轮循环后， 要重新设定y的值。
			// 事实上，主问题中只有y一组决策变量， 把y值求出后强行转换成整数，然后继续迭代下一轮。
			for (int i = 0; i < MAX; i++) 
			{
				double aa = master.getValue(yVar[i]);
				constantY[i] = (int)Math.round(aa);      //  将constantY进行四舍五入
			} // end for
		}//  end while 结束整个Benders       
	}//  end benders_solve()
	
	// 建立主问题和子问题的cplex模型
	public void bendersModel() throws IloException {
		subProblem = new IloCplex();// 子问题
		master = new IloCplex(); // 主问题
		// 参数初始化
        initializeY();
        compute_By();
        compute_bMinusBy();
        
        yVar = new IloNumVar[MAX];
		xDualVar = new IloNumVar[MAX];
		// 参数约束                                                                                                                                                                        变量表达式的名字就叫做subcost
		subcost = master.numVar(0.0, Double.MAX_VALUE, IloNumVarType.Float, "subcost");  //  子问题的表达式（参数）		
		for(int i = 0; i < MAX; ++i)
		{
			xDualVar[i] = subProblem.numVar(0, Double.MAX_VALUE, IloNumVarType.Float, "X_" + i);
			yVar[i] = master.numVar(0, Integer.MAX_VALUE, IloNumVarType.Int, "Y_" + i);
		}

		// 主问题表达式
		IloNumExpr expr0 = master.numExpr();
		for(int i = 0; i < MAX; ++i)
		{
		   expr0 = master.sum(expr0, master.prod(f[i], yVar[i])); 	
		}
		System.out.println("主问题表达式：" + expr0);
		//  整个问题的目标函数： 子问题表达式subcost + 主问题表达式
		master.addMinimize(master.sum(subcost, expr0), "TotalCost");   //  最小化问题，循环中更新上界； 若是最大化问题，则循环中更新下界
	
        //  以下是子问题构造		
		// 子问题目标函数
		IloLinearNumExpr obj = subProblem.linearNumExpr();

		for(int i = 0; i < MAX; ++i)
			obj.addTerm(bMinusBy[i], xDualVar[i]);	
		subobj = subProblem.addMaximize(obj, "dualSubCost");		

		// 子问题约束方程， 每一次循环都添加一个约束	
		for(int i = 0; i < MAX; ++i)
		{
		    IloLinearNumExpr expression = subProblem.linearNumExpr();
		    for(int j = 0; j < MAX; ++j)
		    {
		    	expression.addTerm(At[i][j], xDualVar[j]);
		    }
		    constraints.add(subProblem.addLe(expression, c[i], "C_" + i));
		}		
		// turn off the presolver for the main model
		subProblem.setParam(IloCplex.BooleanParam.PreInd, false);
		subProblem.setParam(IloCplex.Param.RootAlgorithm, IloCplex.Algorithm.Primal);
	}
	
	public static void main(String[] args) throws Exception
	{        new Main8().bendersDecompostion();	}
}
