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
Ӧ������㷨֮ǰ�������ֶ��ֽ�ģ�ͣ��ҳ������⣬ ������Ŀ�꣬ ������Լ��
���ǣ��㷨����Щ������ͨ�ò��֣�����д��ģ�壩�� ��һЩ�����ⲿ�֡� 
������Ϊ��Ҫ�������ڣ� ������һ�������ģ�ͣ�ͨ���ֽ⣬ȷ���������⣬������Ŀ����������Լ��
һ����Ϊ��Ҫ�����⣺ ����������д������������Ļ�������������滮����ô�죿���� ��������Ϊ���Ż��ã� ���޽�Ļ�����λ�ü����ߣ���������
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
    
    int[] constantY = new int[MAX];     //  �����Ĺ̶�yֵ 
    double[] By = new double[MAX];         // ����B*y
    double[] bMinusBy = new double[MAX];   //  ����b-B*y
    
    IloObjective subobj;// ��¼������Ŀ�꺯��
    
    IloNumVar[] xDualVar;  //  x�Ķ�ż����
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
	
	void initializeY()   //  ��yһ����ֵ���̶���, ֻ����һ�Σ��Ժ󽫶�̬����
	{  
		for(int i = 0; i < MAX; ++i)   constantY[i] = 1;
	}
	void compute_By()
	{
		for(int i = 0; i < MAX; ++i) By[i] = 0;   // �ȳ�ʼ��Ϊ0
		for(int i = 0; i < MAX; ++i)
			for(int j = 0; j < MAX; ++j)
				By[i] += B[i][j] * constantY[j];
	}
	void compute_bMinusBy()
	{
		for(int i = 0; i < MAX; ++i)
			bMinusBy[i] = b[i] - By[i];
	}
	// benders�㷨������
	public void benders_solve() throws Exception 
	{
		UB = Double.MAX_VALUE;
		LB = Double.MIN_VALUE;
		while (UB - LB > FUZZ) 
		{
			// �����ɳڵ��������е� ����yֵ����������Ŀ�꺯��. 
			//  ��Ϊy��ֵÿһ�ֶ����������������)�� ������صľ���Ҳ���ˣ��������¼���
			compute_By();
			compute_bMinusBy();
			//  
			IloLinearNumExpr subobj_expr0 = subProblem.linearNumExpr();		
			
			for(int i = 0; i < MAX; ++i)
				subobj_expr0.addTerm(bMinusBy[i], xDualVar[i]);		
			
			subobj.setExpr(subobj_expr0);      // ����������Ŀ�꺯�� ����Ϊy��ֵ���ˡ� obj: (b-By)u
			subProblem.solve();                // ��������Լ��������Ҫ���ã� s.t.  Au <= c
			                                   //  ����ֻ��u�Ǿ��߱�����ʣ�¶��ǳ�����y��ÿ�ֵ�����
			IloCplex.Status status = subProblem.getStatus();			
			// �ж�����������״̬�� �������޽磬����һ��������
			if (status == IloCplex.Status.Unbounded) 
			{
				// �������// ����������һ��������, �����ܵõ���һ�������أ� �Ƿ���ڶ������ߣ�����
				IloLinearNumExpr ray = subProblem.getRay();   //  ���ߴ�subproblem����
				
				System.out.println("getRay returned " + ray.toString());
				// ��¼�����ߵĲ���, ����������е�����Ӧ����IloLinearNumExpr.addTerm()�еĲ�����������ʽ�е�ÿһ�
				IloLinearNumExprIterator it = ray.linearIterator();  
				double[] xCoef = new double[MAX];    //  ��������x��ϵ��, ����ż�������еľ��߱���u��ϵ��			
				while (it.hasNext()) 
				{
					IloNumVar var = it.nextNumVar();       // ���Ӧ���Ƿ��������У����߱�����һ�
					boolean varFound = false;					
					//  ����Լ������
					for (int i = 0; i < MAX && !varFound; i++) {
						if (var.equals(xDualVar[i])) {         //  ��ʾ��ȷ����һ����߱����������equals()������δ��д��
							xCoef[i] = it.getValue();
							varFound = true;
						}
					}
				}		
				double rightHandSide = 0; 		
				double[] temp = new double[MAX];	
				
				// ����Ҫ��ӵ��������Լ������   Ҳ�������� ����ƽ�档 Լ�����̵���ʽ�� (b-By)u <=0  ---->  bu <= yBu , �����һ�������� �Ҳ������Ա��ʽ
				// ���Լ����ֻ��y�Ǳ�����ע�����ʱ���y��Ϊ�����ˣ���Ϊ�����������С����������е�y�ǳ���)��
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
				// ���Լ�����̵��������У� �����ƽ��Ҫ���뵽��������
				System.out.println("\n>>> Adding feasibility cut: " + extremeRayConstraint + "\n");		
			}
			
			else if (status == IloCplex.Status.Optimal) //  ��һ������
			{			
				// �������н⣬�����Ž⼴һ����ֵ��			
				double[] xCoef = new double[MAX];    //  ������x��ϵ��
				//  �õ������(ϵ��),  ע��ͼ���������»�ȡϵ��������
				xCoef = subProblem.getValues(xDualVar);
				
				double rightHandSide = 0; 		
				double[] temp = new double[MAX];				
				// ����Ҫ��ӵ��������Լ������
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
				// ���Լ�����̵���������  (b - By)u <= subcost    ------>   yBu + subcost >= bu
				IloConstraint extremePointConstraint = master.addCut((IloRange)master.ge(expr1, rightHandSide));

				double fTY = 0;	   			
				for(int i = 0; i < MAX; ++i)
					fTY += f[i] * constantY[i];
				//  UB = min{UB, fTY + (b - By)u }
				UB = Math.min(UB, fTY + subProblem.getObjValue());      // ������Ϊ��С���� �����Ͻ�
				System.out.println("\n>>> Adding optimality cut: " + extremePointConstraint + "\n");			
			} 
			else { // unexpected status -- report but do nothing
				   // ���ֲ�ϣ�����ֵ�״̬���Ƿ�
				System.err.println("\n!!! Unexpected subproblem solution status: " + status + "\n");
			}
            //  ���½������⣨�����µ�Լ����,)�� �����½�
			master.solve();      //  �������⣬�����½�  �� ��ԭ�����Ǽ������⣬������Ͻ�
			LB = master.getObjValue();

			// ����������еı���yֵ�� �����Ĺ����У�ʵ�����ǰ�y���ɳڵ��ˡ������õ��ľͲ��������ˣ� ��ÿ��ѭ���� Ҫ�����趨y��ֵ��
			// ��ʵ�ϣ���������ֻ��yһ����߱����� ��yֵ�����ǿ��ת����������Ȼ�����������һ�֡�
			for (int i = 0; i < MAX; i++) 
			{
				double aa = master.getValue(yVar[i]);
				constantY[i] = (int)Math.round(aa);      //  ��constantY������������
			} // end for
		}//  end while ��������Benders       
	}//  end benders_solve()
	
	// ������������������cplexģ��
	public void bendersModel() throws IloException {
		subProblem = new IloCplex();// ������
		master = new IloCplex(); // ������
		// ������ʼ��
        initializeY();
        compute_By();
        compute_bMinusBy();
        
        yVar = new IloNumVar[MAX];
		xDualVar = new IloNumVar[MAX];
		// ����Լ��                                                                                                                                                                        �������ʽ�����־ͽ���subcost
		subcost = master.numVar(0.0, Double.MAX_VALUE, IloNumVarType.Float, "subcost");  //  ������ı��ʽ��������		
		for(int i = 0; i < MAX; ++i)
		{
			xDualVar[i] = subProblem.numVar(0, Double.MAX_VALUE, IloNumVarType.Float, "X_" + i);
			yVar[i] = master.numVar(0, Integer.MAX_VALUE, IloNumVarType.Int, "Y_" + i);
		}

		// ��������ʽ
		IloNumExpr expr0 = master.numExpr();
		for(int i = 0; i < MAX; ++i)
		{
		   expr0 = master.sum(expr0, master.prod(f[i], yVar[i])); 	
		}
		System.out.println("��������ʽ��" + expr0);
		//  ���������Ŀ�꺯���� ��������ʽsubcost + ��������ʽ
		master.addMinimize(master.sum(subcost, expr0), "TotalCost");   //  ��С�����⣬ѭ���и����Ͻ磻 ����������⣬��ѭ���и����½�
	
        //  �����������⹹��		
		// ������Ŀ�꺯��
		IloLinearNumExpr obj = subProblem.linearNumExpr();

		for(int i = 0; i < MAX; ++i)
			obj.addTerm(bMinusBy[i], xDualVar[i]);	
		subobj = subProblem.addMaximize(obj, "dualSubCost");		

		// ������Լ�����̣� ÿһ��ѭ�������һ��Լ��	
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
