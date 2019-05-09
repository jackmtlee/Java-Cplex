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
 * ������Ŀ�꺯�����䣬 Լ�����ˣ�һ�������)�� 
 * ������Լ�����䣬��Ŀ�꺯��ÿһ�ֶ��䣨�������й̶��ı������еĵ�����
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
	//  �洢���е�Լ��
	List<IloConstraint> constraints = new ArrayList<IloConstraint>();
	
    double UB,LB;
    final double FUZZ = 1e-7;
    IloCplex master = null;
    IloCplex subProblem = null;
    IloNumVar subcost = null;
    
    IloObjective subobj = null;   // ��¼������Ŀ�꺯��
    //  ��ż�������еľ��߱���
    IloNumVar[] uVars;
    IloNumVar[] vVars;
    IloNumVar[] wVars;
    //  �������еľ��߱���
    IloNumVar[] yVars = new IloNumVar[MAX];
    IloNumVar[] zVars = new IloNumVar[MAX];
    //  �������й̶����������б仯��y,z��ֵ
    int[] y1 = new int[MAX];
    int[] z1 = new int[MAX];
	// benders�㷨������
	public void benders_solve() throws Exception 
	{
		UB = Double.MAX_VALUE;
		LB = Double.MIN_VALUE;
		while (UB - LB > FUZZ) 
		{	
			// �����ɳڵ��������е� ����yֵ����������Ŀ�꺯��. 
			IloLinearNumExpr subobj_expr0 = subProblem.linearNumExpr();		
			
			for(int i = 0; i < MAX; ++i)
			{
				subobj_expr0.addTerm(demand[i], uVars[i]);
				subobj_expr0.addTerm(-z1[i], vVars[i]);
				subobj_expr0.addTerm(-maxCapacity[i] * y1[i], wVars[i]);
			}	
			
			subobj.setExpr(subobj_expr0);      // ����������Ŀ�꺯�� ����Ϊy��ֵ���ˡ� obj: (b-By)u
			subProblem.solve();                // ��������Լ��������Ҫ���ã� s.t.  Au <= c
			                                   //  ����ֻ��u�Ǿ��߱�����ʣ�¶��ǳ�����y��ÿ�ֵ�����
			IloCplex.Status status = subProblem.getStatus();			
			// �ж�����������״̬�� �������޽磬����һ��������. ��ż�����޽磬˵��ԭ�����޽�(�޿��н�)
			if (status == IloCplex.Status.Unbounded)  // ����϶���ȡ�������ߣ� Ҳ��ȡ������ɣ�����
			{
				//  ��Ȼ�޽磬 ��ô������ֵ�أ����������������� ����Ӧ���������𣿣���
				System.err.println("~~~~~~~~~~unbounded, the value is " + subProblem.getObjValue());
				IloLinearNumExpr ray = subProblem.getRay();   //  �����ߴ�subproblem�Ŀ���������, �˿����򲻱�ɣ�����
				
				System.out.println("getRay returned " + ray.toString());
				IloLinearNumExprIterator it = ray.linearIterator();  
				double[] uCoef = new double[MAX];    //  ��������x��ϵ��, ����ż�������еľ��߱���u��ϵ��	
				double[] vCoef = new double[MAX]; 
				double[] wCoef = new double[MAX]; 
				
//				double[] uCoef1 = new double[MAX];    //  �����е�ϵ���� �϶�Ӧ���м���ɡ�
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
					IloNumVar var = it.nextNumVar();       // ���Ӧ���Ƿ��������У����߱�����һ�
					boolean varFound = false;					
					//  ����Լ������
					for (int i = 0; i < MAX && !varFound; i++) {
						if (var.equals(uVars[i]))
						{         //  ��ʾ��ȷ����һ����߱����������equals()������δ��д����αȽ����������أ���
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
				// ����Ҫ��ӵ��������Լ������   Ҳ�������� ����ƽ�档 Լ�����̵���ʽ�� (b-By)u <=0  ---->  bu <= yBu , �����һ�������� �Ҳ������Ա��ʽ
				// ���Լ����ֻ��y�Ǳ�����ע�����ʱ���y��Ϊ�����ˣ���Ϊ�����������С����������е�y�ǳ���)��
				IloLinearNumExpr expr1 = master.linearNumExpr();
				double rightHandSide = 0;
                for(int i = 0; i < MAX; ++i)
                {
                	expr1.addTerm(-vCoef[i], zVars[i]);
                	expr1.addTerm(-maxCapacity[i] * wCoef[i], yVars[i]);
                	rightHandSide += demand[i] * uCoef[i];
                }
				IloConstraint extremeRayConstraint = master.addCut((IloRange)master.le(expr1, -rightHandSide));
				// ���Լ�����̵��������У� �����ƽ��Ҫ���뵽��������
				System.out.println("\n>>> Adding feasibility cut: " + extremeRayConstraint + "\n");		
			}
			//  extreme points are extreme rays are from feasible region
			//  ��һ�����㡣 ����϶����ҵ����� �� Ҳ�п����ҵ������� polyhedron������֤���ҵ� polytope��
			else if (status == IloCplex.Status.Optimal)
			{			
//				IloLinearNumExpr ray = subProblem.getRay();     //  
//				System.err.println("get ray from optimal senario " + ray.toString());  //  ���޷�ִ�У� ֤��û�м����ߡ�
				System.err.println(isExtremeRayExisted(subProblem)); //  true if there exist extreme rays, false otherwise
				// �������н⣬�����Ž⼴һ����ֵ��			
				double[] uCoef = new double[MAX];    //  ��������x��ϵ��, ����ż�������еľ��߱���u��ϵ��	
				double[] vCoef = new double[MAX]; 
				double[] wCoef = new double[MAX]; 
				//  �õ������(ϵ��),  ע��ͼ���������»�ȡϵ��������
				uCoef = subProblem.getValues(uVars);
				vCoef = subProblem.getValues(vVars);
				wCoef = subProblem.getValues(wVars);
				
				double rightHandSide = 0; 		
				double[] temp = new double[MAX];				
				// ����Ҫ��ӵ��������Լ������
				IloLinearNumExpr expr1 = master.linearNumExpr();
				for(int i = 0; i < MAX; ++i)
				{
                	expr1.addTerm(-vCoef[i], zVars[i]);
                	expr1.addTerm(-maxCapacity[i] * wCoef[i], yVars[i]);
                	rightHandSide += demand[i] * uCoef[i];
				}

				expr1.addTerm(-1, subcost);	
				// ���Լ�����̵���������  (b - By)u <= subcost    ------>   yBu + subcost >= bu
				IloConstraint extremePointConstraint = master.addCut((IloRange)master.le(expr1, -rightHandSide));

				double masterProblemValue = 0;	   			
				for(int i = 0; i < MAX; ++i)
				{
					masterProblemValue += fixedCost[i] * y1[i];
					masterProblemValue += variableCost[i] * z1[i];
				}
				//  UB = min{UB, fTY + (b - By)u }
				UB = Math.min(UB, masterProblemValue + subProblem.getObjValue());      // ������Ϊ��С���� �����Ͻ�
				System.err.println("UB~~~~~~~~~~~~~" + UB);
				System.out.println("\n>>> Adding optimality cut: " + extremePointConstraint + "\n");			
			} 
			else { // unexpected status -- report but do nothing
				   // ���ֲ�ϣ�����ֵ�״̬���Ƿ�
				System.err.println("\n!!! Unexpected subproblem solution status: " + status + "\n");
			}
			
            //  ���½������⣨�����µ�Լ����,)�� �����½�,  MPһ���н硣 �������������޽��ˡ�
			master.solve();      //  �������⣬�����½�  �� ��ԭ�����Ǽ������⣬������Ͻ�
			LB = master.getObjValue();
			
            System.err.println("LB~~~~~~~~~~~~~" + LB);
			// ����������еı���yֵ�� �����Ĺ����У�ʵ�����ǰ�y���ɳڵ��ˡ������õ��ľͲ��������ˣ� ��ÿ��ѭ���� Ҫ�����趨y��ֵ��
			// ��ʵ�ϣ���������ֻ��yһ����߱����� ��yֵ�����ǿ��ת����������Ȼ�����������һ�֡�
			for (int i = 0; i < MAX; i++) 
			{
				double yy = master.getValue(yVars[i]);
				y1[i] = (int)Math.round(yy);      //  ��constantY������������
				double zz = master.getValue(zVars[i]);
				z1[i] = (int)Math.round(zz);
			} // end for
		}//  end while ��������Benders       
	}//  end benders_solve()
	
	// ������������������cplexģ��
	public void bendersModel() throws IloException {
		subProblem = new IloCplex();// ������
		master = new IloCplex(); // ������
		// ������ʼ��
		// ����Լ��                                                                                                                                                                        �������ʽ�����־ͽ���subcost
		subcost = master.numVar(0.0, Double.MAX_VALUE, IloNumVarType.Float, "subcost");  //  ������ı��ʽ��������	
		//  �����y,z Ϊʲôһ��Ҫ�������أ� С��Ϊʲô���У�
		for(int i = 0; i < MAX; ++i)
		{
			yVars[i] = subProblem.numVar(0, 1, IloNumVarType.Int, "Y_" + i);
			zVars[i] = subProblem.numVar(0, maxCapacity[i], IloNumVarType.Int, "Z_" + i);
		}  //  ��ʼ����������߱���

		// ��������ʽ
		IloNumExpr expr0 = master.numExpr();
		for(int i = 0; i < MAX; ++i)
		{
		   expr0 = master.sum(expr0, master.prod(fixedCost[i], yVars[i])); 
		   expr0 = master.sum(expr0, master.prod(variableCost[i], zVars[i]));
		}
		System.out.println("��������ʽ��" + expr0);
		//  ���������Ŀ�꺯���� ��������ʽsubcost + ��������ʽ
		master.addMinimize(master.sum(subcost, expr0), "TotalCost");   //  ��С�����⣬ѭ���и����Ͻ磻 ����������⣬��ѭ���и����½�

        //  �����������⹹��
        uVars = new IloNumVar[MAX];
		vVars = new IloNumVar[MAX];
		wVars = new IloNumVar[MAX];
		// ������Ŀ�꺯��
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

		// ������Լ�����̣� ÿһ��ѭ�������һ��Լ��	(����ط����������⣬ �ֲ���i, j)
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
		// turn off the presolver for the main model�� ����Ĳ���ѡȡ�ر����Ҫ��  ����ѡȡֱ��Ӱ�����ս����
		subProblem.setParam(IloCplex.BooleanParam.PreInd, false);
		subProblem.setParam(IloCplex.Param.RootAlgorithm, IloCplex.Algorithm.Primal);
	}   
	//  ע��cplex��ÿ��ֻ�ܵõ�һ����������ߣ� ���׵õ���һ�����������ǿ��ơ�
	private void outputExtremePointsOrRays(double[] values)   // �����뼫������ȫ�����ڿ������У� �ʣ��������򲻱䣬������Ҳ���䡣
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
	void setYZ()    //  �Ȱ�y,z�̶���Ȼ����benders�ж�̬����
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