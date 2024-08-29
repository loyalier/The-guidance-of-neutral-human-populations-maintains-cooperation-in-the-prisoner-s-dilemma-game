// Prisoners Dilemma game on a small-world graph constructed from a square lattice
// Some players are blocked to give their strategy (other players cannot adopt their strategy)

#define  _CRT_SECURE_NO_WARNINGS

// standard include
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <ctime>
#include <vector>
#include <algorithm>

using namespace std;

// define priority classes
#define NORMAL_PRIORITY_CLASS       0x00000020
#define IDLE_PRIORITY_CLASS         0x00000040
#define HIGH_PRIORITY_CLASS         0x00000080
#define REALTIME_PRIORITY_CLASS     0x00000100

// define parameters
#define L           100      /* lattice size                   */
#define SIZE        (L*L)    /* number of sites                */
#define MC_STEPS    10000   /* run-time in MCS     */
#define OUT_STEPS    500   /* Last 5000 steps  */
//#define r               /* temptation to defect */
#define K           0.1      /* temperature */
#define Q           0      /* Q portion of links are rewired */
#define NAMEOUT     "K4b075r5Q2"
#define RANDOMIZE   3145215
#define NEIMUN      8
#define GROUP_SIZE  4 //每组的人数
#define GROUP_NUM   (SIZE/GROUP_SIZE)  //一共能分多少组
double b;
double para_a = 0.15;  //上层对于下层的影响参数
double payoff_matrix[2][2] = { {1, 0},
							   {b, 0} };

#define update_payoff_matrix(b) payoff_matrix[1][0] = b;

typedef int       tomb1[SIZE];
typedef long int  tomb3[SIZE][NEIMUN];
typedef double    tomb4[SIZE];

tomb1 age_up;  //用不上的数组
tomb1 age_down;  //用不上的数组



tomb1 player_s_up;   //上层玩家的策略
tomb1 player_s_down;  //下层玩家的策略
tomb3 player_n;  //记录玩家的邻居序号

double p[SIZE];  //采用RL的一层各个结点的合作概率
double bt = 1;  //β
double A = 0.5;  //期望

int cnt_s_up[2];  //cnt_s_up[0]记录上层玩家中选择合作的人数，cnt_s_up[1]记录上层玩家中选择背叛的人数
int cnt_s_down[2];  //cnt_s_down[0]记录上层玩家中选择合作的人数，cnt_s_down[1]记录上层玩家中选择背叛的人数
int group[GROUP_NUM][GROUP_SIZE];  //group[i][j]这个数组记录第i组的四个玩家的序号
int player_group[SIZE];  //记录玩家x是哪一组的
int tag_up[SIZE];
int tag_down[SIZE];
int same_down[SIZE];
int same_up[SIZE];

//ofstream outfile1;
ofstream outfile2;


//以下是随机数产生模块，不用管它,直接用就行，用randf()可以直接产生0-1满足均匀分布的随机数，randi(x),产生0---x-1的随机整数
/*************************** RNG procedures ****************************************/
#define NN 624
#define MM 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[NN]; /* the array for the state vector  */
static int mti = NN + 1; /* mti==NN+1 means mt[NN] is not initialized */
void sgenrand(unsigned long seed)
{
	int i;
	for (i = 0; i < NN; i++) {
		mt[i] = seed & 0xffff0000; seed = 69069 * seed + 1;
		mt[i] |= (seed & 0xffff0000) >> 16; seed = 69069 * seed + 1;
	}
	mti = NN;
}
void lsgenrand(unsigned long seed_array[])
{
	int i; for (i = 0; i < NN; i++) mt[i] = seed_array[i]; mti = NN;
}
double genrand()
{
	unsigned long y;
	static unsigned long mag01[2] = { 0x0, MATRIX_A };
	if (mti >= NN)
	{
		int kk;
		if (mti == NN + 1) sgenrand(4357);
		for (kk = 0; kk < NN - MM; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + MM] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		for (; kk < NN - 1; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + (MM - NN)] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		y = (mt[NN - 1] & UPPER_MASK) | (mt[0] & LOWER_MASK);
		mt[NN - 1] = mt[MM - 1] ^ (y >> 1) ^ mag01[y & 0x1];
		mti = 0;
	}
	y = mt[mti++]; y ^= TEMPERING_SHIFT_U(y); y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
	y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C; y ^= TEMPERING_SHIFT_L(y);
	return y;
}

double randf() { return ((double)genrand() * 2.3283064370807974e-10); }
long randi(unsigned long LIM) { return((unsigned long)genrand() % LIM); }

/********************** END of RNG ************************************/


void initial(void)  //初始化策略和合作概率
{
	cnt_s_up[0] = cnt_s_up[1] = 0;  //上下层的合作背叛人数初始化为0
	cnt_s_down[0] = cnt_s_down[1] = 0;
	for (int i = 0; i < SIZE; i++)  //遍历每一个玩家
	{
		int j = randi(2);
		tag_down[i] = j; //初始化下层标签
		tag_up[i] = j; //初始化上层标签
		player_s_up[i] = randi(2);  //初始化上层玩家的策略
		player_s_down[i] = randi(2);  //初始化下层玩家的策略
		cnt_s_up[player_s_up[i]]++;  //数组下标记数法分别统计上下层的合作背叛人数
		cnt_s_down[player_s_down[i]]++;
		p[i] = 0.5;  //初始概率初始化为0.5
	}
}


//找到所有玩家的邻居序号
void prodgraph(void) {
	int x;
	int i, j;
	for (i = 0; i < L; i++)  //第i行
	{
		for (j = 0; j < L; j++)  //第j列
		{
			x = i * L + j;//（从0开始）在网格内从左往右，从上往下的第几个
			player_n[x][0] = i * L + ((j - 1 + L) % L);   //左邻居的序号
			player_n[x][1] = ((i - 1 + L) % L) * L + j;	  //上邻居的序号
			player_n[x][2] = ((i + 1) % L) * L + j;  	  //下邻居的序号
			player_n[x][3] = i * L + ((j + 1) % L);	      //右邻居的序号
			player_n[x][4] = player_n[player_n[x][0]][1]; //左邻居的上邻居，左上
			player_n[x][5] = player_n[player_n[x][0]][2]; //左邻居的下邻居，左下
			player_n[x][6] = player_n[player_n[x][3]][1]; //右邻居的上邻居，右上
			player_n[x][7] = player_n[player_n[x][3]][2]; //右邻居的下邻居，右下
		}
	}
}

//找到每组都有哪些玩家
void sectionalization()
{
	int i;
	for (i = 0; i < GROUP_NUM; i++)
	{
		//每组有四个人，每组的0~3号玩家分别是他自己，右邻居，下邻居，右下角邻居
		group[i][0] = i * 2;
		group[i][1] = player_n[i * 2][3];
		group[i][2] = player_n[i * 2][2];
		group[i][3] = player_n[i * 2][7];
		//上面找到的四个玩家都是第i组的
		player_group[i * 2] = i;
		player_group[player_n[i * 2][3]] = i;
		player_group[player_n[i * 2][2]] = i;
		player_group[player_n[i * 2][7]] = i;
	}
}

void picture_up(int step)//以点阵图的形式记录上层当前的各个玩家的游戏策略
{
	char frequency[100];
	sprintf(frequency, "step=%d,distribution_up.txt", step);
	FILE* p3 = fopen(frequency, "w");
	for (int i = 0; i < L; i++)
	{
		for (int j = 0; j < L; j++)
		{
			if (player_s_up[i * L + j] == 0)//第i+1行第j+1列的玩家
			{
				if (tag_up[i * L + j] == 0)
				{
					fprintf(p3, "0"); //选择合作的0记为0
				}
				else
				{
					fprintf(p3, "1"); //选择合作的1标记为1
				}
			}
			else
			{
				if (tag_up[i * L + j] == 0)
				{
					fprintf(p3, "2"); //选择背叛的0标记为2
				}
				else
				{
					fprintf(p3, "3"); //选择背叛的1标记为3
				}
			}
			if (j != L - 1)//如果不是最后一行，每输出一个数就空一格
			{
				fprintf(p3, " ");
			}
		}
		fprintf(p3, "\n");
	}
	fclose(p3);
}

void picture_down(int step)//以点阵图的形式记录下层当前的各个玩家的游戏策略
{
	char frequency[100];
	sprintf(frequency, "step=%d,distribution_down.txt", step);
	FILE* p3 = fopen(frequency, "w");
	for (int i = 0; i < L; i++)
	{
		for (int j = 0; j < L; j++)
		{
			if (player_s_down[i * L + j] == 0)//第i+1行第j+1列的玩家
			{
				if (tag_down[i * L + j] == 0)
				{
					fprintf(p3, "0"); //选择合作的0记为0
				}
				else
				{
					fprintf(p3, "1"); //选择合作的1标记为1
				}
			}
			else
			{
				if (tag_down[i * L + j] == 0)
				{
					fprintf(p3, "2"); //选择背叛的0标记为2
				}
				else
				{
					fprintf(p3, "3"); //选择背叛的1标记为3
				}
			}
			if (j != L - 1)//如果不是最后一行，每输出一个数就空一格
			{
				fprintf(p3, " ");
			}
		}
		fprintf(p3, "\n");
	}
	fclose(p3);
}


double payoff_up(int x) {//上层更新收益
	double pay = 0;
	if (tag_up[x] == 0) //如果这个上层玩家标签为0
	{
		for (int i = 0; i < 4; i++) //在他的四个邻居里
		{
			if (tag_up[player_n[x][i]] == 0)  //找到标签也是0的玩家进行交互
			{
				pay += payoff_matrix[player_s_up[x]][player_s_up[player_n[x][i]]];
				same_up[x]++;
			}
		}
	}
	if (tag_up[x] == 1)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_up[player_n[x][i]] == 1)
			{
				pay += payoff_matrix[player_s_up[x]][player_s_up[player_n[x][i]]];
				same_up[x]++;
			}
		}
	}
	return pay;
}

double payoff_down(int x) {//下层更新收益
	double pay = 0;
	if (tag_down[x] == 0)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_down[player_n[x][i]] == 0)
			{
				pay += payoff_matrix[player_s_down[x]][player_s_down[player_n[x][i]]];
				same_down[x]++;
			}
		}
	}
	if (tag_down[x] == 1)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_down[player_n[x][i]] == 1)
			{
				pay += payoff_matrix[player_s_down[x]][player_s_down[player_n[x][i]]];
				same_down[x]++;
			}
		}
	}
	return pay;
}

double fitness_up(int x)  //上层的适应度，返回收益的加权平均数
{
	double r, t;
	if (same_down[x] == 0) //如果对应的下层的这个是一个孤立节点，那么适应度就是自身的收益
	{
		r = payoff_up(x) / 4;
	}
	else //不然适应度就是上下收益的加权平均数
	{
		t = payoff_down(x) / 4; //下层的平均收益
		r = para_a * t + (1 - para_a) * payoff_up(x) / 4;
	}
	return r;
}

double stimu(int x)
{
	double s, r;
	r = fitness_up(x);
	s = tanh(bt * (r - A));
	return s;
}

//计算x更新策略的概率
void calcul(int x)
{
	int i;
	double s;
	i = x;
	s = stimu(i);
	if ((s >= 0) && player_s_up[i] == 0)
	{
		p[i] = p[i] + (1 - p[i]) * s;
	}
	else if ((s < 0) && player_s_up[i] == 0)
	{
		p[i] = p[i] + p[i] * s;
	}
	else if ((s >= 0) && player_s_up[i] == 1)
	{
		p[i] = p[i] - p[i] * s;
	}
	else
	{
		p[i] = p[i] - (1 - p[i]) * s;
	}
}

double fitness_down(int x)    //计算下层的适应度
{
    double payoff = 0.2 * payoff_up(x);
    for (int i = 0; i < 4; i++)
    {
        payoff = payoff + 0.2 * payoff_up(player_n[x][i]);
    }
	return para_a * payoff_up(x) + (1 - para_a) * payoff_down(x);
}

void update_up(int x)  //上层BM进行策略更新
{
	calcul(x);
	if (randf() <= p[x]) //策略更新
	{
		cnt_s_up[player_s_up[x]]--;
		player_s_up[x] = 0;
		cnt_s_up[player_s_up[x]]++;
	}
	else
	{
		cnt_s_up[player_s_up[x]]--;
		player_s_up[x] = 1;
		cnt_s_up[player_s_up[x]]++;
	}
	int y;
	double prob_down = 0;
	y = player_n[x][int(randi(4))];
	if (tag_up[x] != tag_up[y])
	{
		prob_down = 1 / (1 + exp((payoff_up(x) - payoff_up(y)) / K));
		if (randf() < prob_down)
			tag_up[x] = tag_up[y]; //标签更新
	}
	return;
}

void update_down(int x)  //下层费米进行策略更新
{
	int y;
	double prob_down = 0;	// Probability of updating, initial not update
	y = player_n[x][int(randi(4))];
	if (player_s_down[x] != player_s_down[y])
	{
		prob_down = 1 / (1 + exp((fitness_down(x) - fitness_down(y)) / K));
		if (randf() < prob_down)
		{
			cnt_s_down[player_s_down[x]]--;	// Old strategy
			player_s_down[x] = player_s_down[y];
			cnt_s_down[player_s_down[x]]++;	// New strategy
			tag_down[x] = tag_down[y];  //学习标签
		}
	}
}

void game(void) //进行博弈
{
	int n = SIZE;
	vector<int> nums(n);
	for (int i = 0; i < n; ++i)
	{
		nums[i] = i;
	}
	srand(time(0));
	for (int i = n - 1; i > 0; --i)
	{
		int j = rand() % (i + 1);
		swap(nums[i], nums[j]);
	}
	for (int i = 0; i < SIZE; i++)
	{
		int x = nums[i];  //随机选择一个位置
		update_up(x);  //更新上层
		update_down(x);  //更新下层
	}
}

void count_of_c1c2d1d2(int steps) //记录第x步时c1，c2，d1，d2各占多少
{
	char frequency[100];
	double c1, c2, d1, d2;
	c1 = c2 = d1 = d2 = 0;
	double p_c1 = 0; //分别记录c1,c2,d1,d2的数量
	double p_c2 = 0;
	double p_d1 = 0;
	double p_d2 = 0; //分别记录c1,c2,d1,d2的比例
	for (int i = 0; i < SIZE; i++)
	{
		if ((tag_up[i] == 0) && (player_s_up[i] == 0))
			c1++;
		if ((tag_up[i] == 0) && (player_s_up[i] == 1))
			d1++;
		if ((tag_up[i] == 1) && (player_s_up[i] == 0))
			c2++;
		if ((tag_up[i] == 1) && (player_s_up[i] == 1))
			d2++;
	}
	p_c1 = c1 / SIZE;
	p_c2 = c2 / SIZE;
	p_d1 = d1 / SIZE;
	p_d2 = d2 / SIZE;
	sprintf(frequency, "b=%g_a=%g_c1c2d1d2.txt", b, para_a);
	FILE* outfile3 = fopen(frequency, "a");
	fprintf(outfile3, "%d\t %lf\t %lf\t %lf\t %lf\n", steps, p_c1, p_c2, p_d1, p_d2);
	fclose(outfile3);
	if (steps == MC_STEPS - 1) //最后一步统计最终的比例
	{
		sprintf(frequency, "final_proportion_of_c1c2d1d2.txt");
		FILE* outfile3 = fopen(frequency, "a");
		fprintf(outfile3, "%lf\t %lf\t %lf\t %lf\t %lf\t %lf\n", para_a, b, p_c1, p_c2, p_d1, p_d2);
		fclose(outfile3);
	}
}

void pair_of_up_and_down(int steps) //统计第x步时上下的合作对背叛对的数量
{
	int cc, cd, dc, dd; //分别记录上合作下合作，上合作下背叛，上背叛下合作，上背叛下背叛的个数
	cc = cd = dc = dd = 0;
	char frequency[100];
	for (int i = 0; i < SIZE; i++)
	{
		if ((player_s_up[i] == 0) && (player_s_down[i] == 0))
			cc++;
		if ((player_s_up[i] == 0) && (player_s_down[i] == 1))
			cd++;
		if ((player_s_up[i] == 1) && (player_s_down[i] == 0))
			dc++;
		if ((player_s_up[i] == 1) && (player_s_down[i] == 1))
			dd++;
	}
	sprintf(frequency, "b=%g_a=%g_pair_of_up_and_down_steps", b, para_a);
	FILE* outfile3 = fopen(frequency, "a");
	fprintf(outfile3, "%d\t %d\t %d\t %d\t %d\n", steps, cc, cd, dc, dd);
	fclose(outfile3);
	if (steps == MC_STEPS - 1) //最后一步统计最终的数量
	{
		sprintf(frequency, "final_count_of_pair_of_up_and_down.txt");
		FILE* outfile3 = fopen(frequency, "a");
		fprintf(outfile3, "%lf\t %lf\t %d\t %d\t %d\t %d\n", para_a, b, cc, cd, dc, dd);
		fclose(outfile3);
	}
}

int main()
{
	int steps;
	double fc_up, fc_down, last_sum_up, last_sum_down, avg_fc_up, avg_fc_down;
	//outfile1.open("frequency.txt");
	outfile2.open("average.txt");
	if (!outfile2)
	{
		cout << "can not open";
		abort();
	}
	// initialize the random number generation
	sgenrand(RANDOMIZE);
	prodgraph();
	sectionalization();
	para_a = 0.2;

	//for (para_a = 0; para_a <= 1.01; para_a += 0.1)
	for (b = 1.0; b <= 1.51; b += 0.005)
	{
		for (para_a = 0; para_a <= 1.01; para_a += 0.1)
			//for (b = 1.0; b <= 2.01; b += 0.01)
		{
			avg_fc_up = last_sum_up = avg_fc_down = last_sum_down = 0;
			update_payoff_matrix(b);
			initial();
			char frequency[100];
			sprintf(frequency, "b=%g_a=%g_frequency.txt", b, para_a);
			FILE* outfile1 = fopen(frequency, "w");
			for (steps = 0; steps < MC_STEPS; steps++)
			{
				game();
				fc_up = (double)cnt_s_up[0] / SIZE;	// OLD: tongji()
				fc_down = (double)cnt_s_down[0] / SIZE;
				//outfile1<<steps<<'\t'<<fc_up<<'\t'<<fc_down<<endl;	// Output: frequency
				fprintf(outfile1, "%d\t%lf\t%lf\n", steps, fc_up, fc_down);
				if (steps > MC_STEPS - OUT_STEPS - 1)
				{
					last_sum_up += fc_up;
					last_sum_down += fc_down;
				}
				count_of_c1c2d1d2(steps);
				pair_of_up_and_down(steps);
                /*if (steps == 1000)
					picture_up(1000);
                if (steps == 2000)
					picture_up(2000);
                if (steps == 3000)
					picture_up(3000);
				if (steps == 4000)
					picture_up(4000);*/
			}
			avg_fc_up = (double)last_sum_up / OUT_STEPS;
			avg_fc_down = (double)last_sum_down / OUT_STEPS;

			cout << b << "\t" << para_a << "\t" << avg_fc_up << '\t' << avg_fc_down << endl;
			outfile2 << b << "\t" << para_a << "\t" << avg_fc_up << '\t' << avg_fc_down << endl;
			fclose(outfile1);
			//if (fabs(avg_fc_down) < 1e-7 || fabs(avg_fc_down) < 1e-7) break;
		}
	}

	outfile2.close();
	return 0;
}

