#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <Windows.h>
#include <stdarg.h>
#include <ctype.h>					
#include <stdbool.h>

/*==========宏定义==========*/
#define MAXN 600                  // 站点最大数量
#define MAXS 30                   // 站点名称最大长度
#define MAXL 64                   // 线路最大数量
#define MAXVIA 5                  // 最大途经站点数量
#define INF 0x3f3f3f3f            // 无穷大
#define LOG_FILE "rout_log.txt"   // 日志文件名
#define LOG_BUF_SIZE 8192         // 日志缓冲区大小

/*==========颜色宏==========*/
#define COL_TITLE FOREGROUND_BLUE | FOREGROUND_INTENSITY
#define COL_MENU FOREGROUND_GREEN | FOREGROUND_RED | FOREGROUND_BLUE | FOREGROUND_INTENSITY
#define COL_INPUT FOREGROUND_GREEN | FOREGROUND_INTENSITY
#define COL_TRANS FOREGROUND_RED |FOREGROUND_GREEN |FOREGROUND_INTENSITY
#define COL_ARRIVE FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_INTENSITY
#define COL_EXIT FOREGROUND_RED | FOREGROUND_INTENSITY
#define COL_VIA FOREGROUND_BLUE | FOREGROUND_GREEN | FOREGROUND_INTENSITY

/*==========全局数据==========*/
typedef struct {			// 站点结构体
	char station_name[MAXS];// 站点名称
	int  line[MAXL];		// 站点所属线路
	int station_id;			// 站点编号
	bool is_transfer;		// 是否为换乘站
	bool is_great;			// 是否为大型站点
} Station;

typedef struct {			// 线路结构体
	int line_id;            // 线路编号
	char line_name[MAXS];   // 线路名称
	int station_count;      // 线路站点数量
	int stations[MAXN];     // 线路经过的站点编号
	bool is_fast;			// 是否为快速线路
	bool is_surban;			// 是否为郊区线路
} Line;

typedef struct {			// 权重配置结构体
	char mode_name[MAXS];   // 模式名称
	int bases_stop_cost;    // 每站基础成本（秒）
	int bases_surban_cost;  // 郊区线路附加成本（秒）
	int transfer_base_penalty;// 换乘基础惩罚（秒）
	int transfer_great_bouns;// 大站换乘额外惩罚（秒）
	int fast_line_discount; // 快速线路折扣（百分比）
	int peak_hour_multiplier; // 高峰时段惩罚倍数（百分比）
} WeighProfile;

/*==========全局变量==========*/
Station stations[MAXN];		// 站点数组
Line lines[MAXL];		    // 线路数组
WeighProfile profiles[] = {
	{"极致少换乘", 90, 60, 1200, 150, 50, 120},
	{"时间最优先", 90, 60, 800, 100, 50, 110},
	{"均衡舒适", 90, 60, 1000, 150, 50, 120}
};
unsigned long long LineMask[MAXN][MAXN]; // 线路掩码邻接矩阵
int Connect[MAXN][MAXN];	// 站点连接矩阵
int station_count = 0;		// 站点数量
int line_count = 0;			// 线路数量
int current_mode = 0;		// 当前模式索引

/*==========静态变量==========*/
static char log_buffer[LOG_BUF_SIZE];
static int lastQueryFrom = -1;
static int lastQueryTo = -1;
static char lastQueryFromName[MAXS];
static char lastQueryToName[MAXS];
static int lastQueryViaCount = 0;
static int lastQueryViaIdx[MAXVIA];
static char lastQueryViaNames[MAXVIA][MAXS];
static int dist[MAXN], prev[MAXN];
static bool done[MAXN];
static int stk[MAXN], top;

// 新增：记录最短路径中到达每个站点所使用的线路
static int best_line[MAXN];

/*==========函数声明==========*/
static void SetColor(WORD color);
static void ResetColor();
static void cPrintf(WORD color, const char* format, ...);
static void discard_stdin();
static int get_station_id_by_name(const char* station_name);
static int get_line_id_by_name(const char* line_name);
int findStation(const char* name);
int fuzzyMatch(const char* input, const char* target);
int fuzzyFindStation(const char* prompt, char* result);
unsigned long long get_edge_line_mask(int from, int to); // 修改：返回掩码而非单一线路
bool is_peak_hour();
void dijkstra(int start, int end);
void routePrint(int start, int end, int* viaList, int viaCount);
void routeQuery();
void repeatLastQuery();
void saveLog();
void showMenu();
void switchMode();
void loadData();
void choiceFunction();
void listAllLines();

/*==========函数定义==========*/
static void SetColor(WORD color) {
	HANDLE hConsole = GetStdHandle(STD_OUTPUT_HANDLE);
	SetConsoleTextAttribute(hConsole, color);
}

static void ResetColor() {
	HANDLE hConsole = GetStdHandle(STD_OUTPUT_HANDLE);
	SetConsoleTextAttribute(hConsole, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
}

static void cPrintf(WORD color, const char* format, ...) {
	char buffer[2048];
	va_list args;
	va_start(args, format);
	vsnprintf(buffer, sizeof(buffer), format, args);
	va_end(args);
	SetColor(color);
	fputs(buffer, stdout);
	ResetColor();
}

static void discard_stdin() {
	int c;
	while ((c = getchar()) != '\n' && c != EOF) {}
}

static int get_station_id_by_name(const char* station_name) {
	if (station_count >= MAXN) {
		cPrintf(COL_EXIT, "站点数量已达上限！\n");
		return -1;
	}
	for (int i = 0; i < station_count; i++) {
		if (strcmp(stations[i].station_name, station_name) == 0) {
			return stations[i].station_id;
		}
	}
	strcpy_s(stations[station_count].station_name, sizeof(stations[station_count].station_name), station_name);
	stations[station_count].station_id = station_count;
	stations[station_count].is_transfer = false;
	stations[station_count].is_great = false;
	memset(stations[station_count].line, 0, sizeof(stations[station_count].line));
	return station_count++;
}

static int get_line_id_by_name(const char* line_name) {
	if (line_count >= MAXL) {
		cPrintf(COL_EXIT, "线路数量已达上限！\n");
		return -1;
	}
	for (int i = 0; i < line_count; i++) {
		if (strcmp(lines[i].line_name, line_name) == 0) {
			return lines[i].line_id;
		}
	}
	strcpy_s(lines[line_count].line_name, sizeof(lines[line_count].line_name), line_name);
	lines[line_count].line_id = line_count;
	lines[line_count].station_count = 0;
	lines[line_count].is_fast = false;
	lines[line_count].is_surban = false;
	return line_count++;
}

int findStation(const char* name) {
	for (int i = 0; i < station_count; i++) {
		if (strcmp(stations[i].station_name, name) == 0) {
			return stations[i].station_id;
		}
	}
	return -1;
}

int fuzzyMatch(const char* input, const char* target) {
	char input_lower[MAXS], target_lower[MAXS];
	int i;
	for (i = 0; input[i] != '\0' && i < MAXS - 1; i++) {
		input_lower[i] = tolower((unsigned char)input[i]);
	}
	input_lower[i] = '\0';
	for (i = 0; target[i] != '\0' && i < MAXS - 1; i++) {
		target_lower[i] = tolower((unsigned char)target[i]);
	}
	target_lower[i] = '\0';
	return strstr(target_lower, input_lower) != NULL;
}

int fuzzyFindStation(const char* prompt, char* result) {
	char input[MAXS];
	while (1) {
		cPrintf(COL_INPUT, "%s", prompt);
		if (scanf_s("%29s", input, (unsigned)sizeof(input)) != 1) {
			discard_stdin();
			cPrintf(COL_EXIT, "输入失败，请重试！\n");
			continue;
		}
		discard_stdin();

		int exactIdx = findStation(input);
		if (exactIdx != -1) {
			strcpy_s(result, MAXS, stations[exactIdx].station_name);
			return exactIdx;
		}

		int candidates[MAXN], count = 0;
		for (int i = 0; i < station_count; i++) {
			if (fuzzyMatch(input, stations[i].station_name)) {
				candidates[count++] = stations[i].station_id;
			}
		}

		if (count == 0) {
			cPrintf(COL_EXIT, "未找到匹配站点，请重试！\n");
		}
		else if (count == 1) {
			strcpy_s(result, MAXS, stations[candidates[0]].station_name);
			cPrintf(COL_MENU, "匹配到: %s\n", result);
			return candidates[0];
		}
		else {
			cPrintf(COL_MENU, "找到 %d 个匹配站点：\n", count);
			for (int i = 0; i < count && i < 10; i++) {
				cPrintf(COL_TRANS, "  %d. %s\n", i + 1, stations[candidates[i]].station_name);
			}
			if (count > 10) {
				cPrintf(COL_MENU, "  ...（显示前10个）\n");
			}
			cPrintf(COL_INPUT, "请选择编号（0重输）：");
			int choice;
			if (scanf_s("%d", &choice) != 1) {
				discard_stdin();
				cPrintf(COL_EXIT, "输入无效！\n");
				continue;
			}
			discard_stdin();

			if (choice > 0 && choice <= count) {
				strcpy_s(result, MAXS, stations[candidates[choice - 1]].station_name);
				return candidates[choice - 1];
			}
			else if (choice == 0) {
				continue;
			}
			else {
				cPrintf(COL_EXIT, "无效选择！\n");
			}
		}
	}
	return -1;
}

/**
 * @brief 获取连接两站点的所有线路的掩码
 * 修改原函数，返回线路掩码而非单一线路ID
 */
unsigned long long get_edge_line_mask(int from, int to) {
	return LineMask[from][to];
}

bool is_peak_hour() {
	time_t now = time(NULL);
	struct tm tm_info;
	localtime_s(&tm_info, &now);
	int hour = tm_info.tm_hour;
	return (hour >= 7 && hour <= 9) || (hour >= 17 && hour <= 19);
}

/**
 * @brief Dijkstra最短路径算法（修复版）
 * 核心修复：现在会检查所有连接u和v的线路，并选择最优线路
 * 同时记录到达每个站点所使用的线路
 */
void dijkstra(int start, int end) {
	// 初始化距离数组和路径记录
	for (int i = 0; i < station_count; i++) {
		dist[i] = INF;
		prev[i] = -1;
		best_line[i] = -1;  // 新增：记录到达i站所使用的线路
		done[i] = false;
	}
	dist[start] = 0;
	best_line[start] = -1;  // 起点无线路

	// 检查当前是否为高峰时段
	bool peak = is_peak_hour();

	while (true) {
		// 寻找未访问的最小距离节点
		int u = -1, best = INF;
		for (int i = 0; i < station_count; i++) {
			if (!done[i] && dist[i] < best) {
				best = dist[i];
				u = i;
			}
		}
		if (u == -1 || u == end) break;
		done[u] = true;

		// 松弛操作：遍历所有相邻站点
		for (int v = 0; v < station_count; v++) {
			if (!Connect[u][v]) continue;

			// 获取连接u和v的所有线路的掩码
			unsigned long long mask = LineMask[u][v];
			if (mask == 0) continue;  // 无线路连接

			// 遍历所有可能的线路
			for (int line = 0; line < line_count; line++) {
				if (!(mask & (1ULL << line))) continue;  // 该线路不连接u和v

				// ====== 权重计算开始 ======
				WeighProfile* profile = &profiles[current_mode];
				int cost = profile->bases_stop_cost;

				// 1. 郊区线路附加成本
				if (lines[line].is_surban) {
					cost += profile->bases_surban_cost;
				}

				// 2. 快速线路折扣
				if (lines[line].is_fast) {
					cost = cost * profile->fast_line_discount / 100;
				}

				// 3. 高峰时段惩罚
				if (peak) {
					cost = cost * profile->peak_hour_multiplier / 100;
				}

				// 4. 换乘惩罚：比较当前线路与到达u站所使用的线路
				if (best_line[u] != -1 && best_line[u] != line) {
					cost += profile->transfer_base_penalty;
					if (stations[u].is_great) {
						cost += profile->transfer_great_bouns;
					}
				}
				// ====== 权重计算结束 ======

				// 如果找到更优路径，更新距离、前驱节点和所用线路
				if (dist[u] + cost < dist[v]) {
					dist[v] = dist[u] + cost;
					prev[v] = u;
					best_line[v] = line;  // 记录到达v站所使用的线路
				}
			}
		}
	}

	// 构建路径栈（从终点回溯到起点）
	top = 0;
	for (int x = end; x != -1; x = prev[x]) {
		stk[top++] = x;
	}
}

/**
 * @brief 打印路径详情（修复版）
 * 现在使用best_line数组获取准确的线路信息
 */
void routePrint(int start, int end, int* viaList, int viaCount) {
	if (top == 0 || dist[end] == INF) {
		cPrintf(COL_EXIT, "\n两站间暂无可达路线\n");
		char tmp[256];
		snprintf(tmp, sizeof(tmp), "两站间暂无可达路线\n");
		strcat_s(log_buffer, LOG_BUF_SIZE, tmp);
		return;
	}

	cPrintf(COL_MENU, "\n【%s】\n", profiles[current_mode].mode_name);
	char tmp[512];
	snprintf(tmp, sizeof(tmp), "【%s】\n", profiles[current_mode].mode_name);
	strcat_s(log_buffer, LOG_BUF_SIZE, tmp);

	// 统计实际换乘次数和站数（使用best_line数组）
	int actualTransfers = 0, actualStops = 0;
	int curLine = -1;

	// 从起点到终点遍历路径栈
	for (int i = top - 1; i >= 0; i--) {
		int station = stk[i];
		int line = best_line[station];  // 到达该站所使用的线路

		if (line == -1) continue;  // 起点站，跳过

		actualStops++;
		if (curLine == -1) {
			curLine = line;
		}
		else if (line != curLine) {
			actualTransfers++;
			curLine = line;
		}
	}

	cPrintf(COL_TRANS, "换乘 %d 次", actualTransfers);
	cPrintf(COL_MENU, "， %d 站\n\n", actualStops);
	snprintf(tmp, sizeof(tmp), "换乘 %d 次， %d 站\n\n", actualTransfers, actualStops);
	strcat_s(log_buffer, LOG_BUF_SIZE, tmp);

	if (top <= 0) {
		cPrintf(COL_EXIT, "\n路径构建失败\n");
		return;
	}

	// 输出路径详情（使用best_line数组）
	int last = start;
	curLine = -1;
	int ride = 0;

	// 从起点到终点遍历（stk数组是逆序的）
	for (int idx = top - 1; idx >= 0; idx--) {
		int now = stk[idx];
		int segLine = best_line[now];  // 获取当前段所使用的线路

		// 起点站无线路信息
		if (segLine == -1) {
			last = now;
			continue;
		}

		if (curLine == -1) {
			curLine = segLine;
		}
		else if (segLine != curLine) {
			// 线路变化，打印上一段行程
			cPrintf(COL_TRANS, "  乘坐%s %d站 → %s换乘\n",
				lines[curLine].line_name, ride, stations[last].station_name);
			snprintf(tmp, sizeof(tmp), "  乘坐%s %d站 → %s换乘\n",
				lines[curLine].line_name, ride, stations[last].station_name);
			strcat_s(log_buffer, LOG_BUF_SIZE, tmp);
			curLine = segLine;
			ride = 0;
		}
		ride++;

		// 检查是否为途经站
		bool isVia = false;
		for (int i = 0; i < viaCount; i++) {
			if (now == viaList[i]) {
				isVia = true;
				break;
			}
		}
		if (isVia) {
			cPrintf(COL_VIA, "  [经停站：%s]\n", stations[now].station_name);
			snprintf(tmp, sizeof(tmp), "  [经停站：%s]\n", stations[now].station_name);
			strcat_s(log_buffer, LOG_BUF_SIZE, tmp);
		}

		last = now;
	}

	// 打印最后一段行程
	if (curLine != -1) {
		cPrintf(COL_ARRIVE, "  乘坐%s %d站 → 到达%s\n",
			lines[curLine].line_name, ride, stations[end].station_name);
		snprintf(tmp, sizeof(tmp), "  乘坐%s %d站 → 到达%s\n",
			lines[curLine].line_name, ride, stations[end].station_name);
		strcat_s(log_buffer, LOG_BUF_SIZE, tmp);
	}

	cPrintf(COL_MENU, "\n总乘车距离：%d 站\n\n", actualStops);
	snprintf(tmp, sizeof(tmp), "总乘车距离：%d 站\n\n", actualStops);
	strcat_s(log_buffer, LOG_BUF_SIZE, tmp);
}

void routeQuery() {
	cPrintf(COL_MENU, "\n========== 路线查询 ==========\n");

	char startName[MAXS], endName[MAXS];
	int viaIdx[MAXVIA] = { 0 };
	int viaCount = 0;
	char viaNames[MAXVIA][MAXS] = { 0 };

	int startIdx = fuzzyFindStation("请输入起点站名：", startName);

	char choice[10];
	cPrintf(COL_INPUT, "是否添加途经站？(y/n): ");
	if (scanf_s("%9s", choice, 10) != 1) {
		choice[0] = 'n';
	}
	discard_stdin();

	if (choice[0] == 'y' || choice[0] == 'Y') {
		while (1) {
			cPrintf(COL_INPUT, "请输入途经站数量（1-%d）：", MAXVIA);
			if (scanf_s("%d", &viaCount) == 1 && viaCount >= 1 && viaCount <= MAXVIA) {
				break;
			}
			cPrintf(COL_EXIT, "输入无效！请输入1-%d之间的数字。\n", MAXVIA);
			discard_stdin();
		}
		discard_stdin();

		for (int i = 0; i < viaCount; i++) {
			cPrintf(COL_VIA, "[途经站 #%d]\n", i + 1);
			viaIdx[i] = fuzzyFindStation("请输入站名：", viaNames[i]);
		}
	}

	int endIdx = fuzzyFindStation("请输入终点站名：", endName);

	log_buffer[0] = '\0';

	int totalStops = 0, totalTransfers = 0;
	int currentFrom = startIdx;
	char currentFromName[MAXS];
	strcpy_s(currentFromName, sizeof(currentFromName), startName);

	char header[256];
	if (viaCount > 0) {
		snprintf(header, sizeof(header), "\n-----------多站经停查询：%s → ", startName);
		strcat_s(log_buffer, LOG_BUF_SIZE, header);
		for (int i = 0; i < viaCount; i++) {
			snprintf(header, sizeof(header), "%s → ", viaNames[i]);
			strcat_s(log_buffer, LOG_BUF_SIZE, header);
		}
		snprintf(header, sizeof(header), "%s ----------\n", endName);
		strcat_s(log_buffer, LOG_BUF_SIZE, header);
	}
	else {
		snprintf(header, sizeof(header), "\n-----------单站查询：%s → %s ----------\n", startName, endName);
		strcat_s(log_buffer, LOG_BUF_SIZE, header);
	}

	for (int i = -1; i < viaCount; i++) {
		int segmentEnd = (i == viaCount - 1) ? endIdx : viaIdx[i + 1];
		const char* segmentEndName = (i == viaCount - 1) ? endName : viaNames[i + 1];

		dijkstra(currentFrom, segmentEnd);

		if (top == 0 || dist[segmentEnd] == INF) {
			cPrintf(COL_EXIT, "\n%s → %s 无可达路线，查询终止！\n", currentFromName, segmentEndName);
			return;
		}

		routePrint(currentFrom, segmentEnd, viaIdx, viaCount);

		int segTransfers = 0;
		int curLine = -1;
		for (int j = top - 1; j > 0; j--) {
			totalStops++;
			int line = best_line[stk[j]];  // 修改：使用best_line数组
			if (curLine == -1) curLine = line;
			else if (line != curLine) {
				segTransfers++;
				curLine = line;
			}
		}
		totalTransfers += segTransfers;

		currentFrom = segmentEnd;
		strcpy_s(currentFromName, sizeof(currentFromName), segmentEndName);
	}

	if (viaCount > 0) {
		cPrintf(COL_TITLE, "\n-------------------- 全程总计 --------------------\n");
		cPrintf(COL_MENU, "途经站数：%d 个\n", viaCount);
		cPrintf(COL_TRANS, "总换乘次数：%d 次\n", totalTransfers);
		cPrintf(COL_MENU, "总站点数：%d 站\n\n", totalStops);

		char summary[512];
		snprintf(summary, sizeof(summary),
			"\n-------------------- 全程总计 --------------------\n"
			"途经站数：%d 个\n"
			"总换乘次数：%d 次\n"
			"总站点数：%d 站\n",
			viaCount, totalTransfers, totalStops);
		strcat_s(log_buffer, LOG_BUF_SIZE, summary);
	}

	lastQueryFrom = startIdx;
	lastQueryTo = endIdx;
	strcpy_s(lastQueryFromName, sizeof(lastQueryFromName), startName);
	strcpy_s(lastQueryToName, sizeof(lastQueryToName), endName);
	lastQueryViaCount = viaCount;
	for (int i = 0; i < viaCount; i++) {
		lastQueryViaIdx[i] = viaIdx[i];
		strcpy_s(lastQueryViaNames[i], MAXS, viaNames[i]);
	}
}

void repeatLastQuery() {
	if (lastQueryFrom == -1) {
		cPrintf(COL_EXIT, "\n无上次查询记录，请先进行一次查询！\n");
		return;
	}

	cPrintf(COL_MENU, "\n========== 重复上次查询 ==========\n");
	log_buffer[0] = '\0';

	int currentFrom = lastQueryFrom;
	char currentFromName[MAXS];
	strcpy_s(currentFromName, sizeof(currentFromName), lastQueryFromName);

	if (lastQueryViaCount > 0) {
		char header[256];
		snprintf(header, sizeof(header), "\n-----------多站经停查询：%s → ", lastQueryFromName);
		strcat_s(log_buffer, LOG_BUF_SIZE, header);
		for (int i = 0; i < lastQueryViaCount; i++) {
			snprintf(header, sizeof(header), "%s → ", lastQueryViaNames[i]);
			strcat_s(log_buffer, LOG_BUF_SIZE, header);
		}
		snprintf(header, sizeof(header), "%s ----------\n", lastQueryToName);
		strcat_s(log_buffer, LOG_BUF_SIZE, header);
	}
	else {
		char header[256];
		snprintf(header, sizeof(header), "\n-----------单站查询：%s → %s ----------\n", lastQueryFromName, lastQueryToName);
		strcat_s(log_buffer, LOG_BUF_SIZE, header);
	}

	int totalStops = 0, totalTransfers = 0;

	for (int i = -1; i < lastQueryViaCount; i++) {
		int segmentEnd = (i == lastQueryViaCount - 1) ? lastQueryTo : lastQueryViaIdx[i + 1];
		const char* segmentEndName = (i == lastQueryViaCount - 1) ? lastQueryToName : lastQueryViaNames[i + 1];

		dijkstra(currentFrom, segmentEnd);

		if (top == 0 || dist[segmentEnd] == INF) {
			cPrintf(COL_EXIT, "\n%s → %s 无可达路线，查询终止！\n", currentFromName, segmentEndName);
			return;
		}

		routePrint(currentFrom, segmentEnd, lastQueryViaIdx, lastQueryViaCount);

		int segTransfers = 0;
		int curLine = -1;
		for (int j = top - 1; j > 0; j--) {
			totalStops++;
			int line = best_line[stk[j]];  // 修改：使用best_line数组
			if (curLine == -1) curLine = line;
			else if (line != curLine) {
				segTransfers++;
				curLine = line;
			}
		}
		totalTransfers += segTransfers;

		currentFrom = segmentEnd;
		strcpy_s(currentFromName, sizeof(currentFromName), segmentEndName);
	}

	if (lastQueryViaCount > 0) {
		cPrintf(COL_TITLE, "\n-------------------- 全程总计 --------------------\n");
		cPrintf(COL_MENU, "途经站数：%d 个\n", lastQueryViaCount);
		cPrintf(COL_TRANS, "总换乘次数：%d 次\n", totalTransfers);
		cPrintf(COL_MENU, "总站点数：%d 站\n\n", totalStops);

		char summary[512];
		snprintf(summary, sizeof(summary),
			"\n-------------------- 全程总计 --------------------\n"
			"途经站数：%d 个\n"
			"总换乘次数：%d 次\n"
			"总站点数：%d 站\n",
			lastQueryViaCount, totalTransfers, totalStops);
		strcat_s(log_buffer, LOG_BUF_SIZE, summary);
	}
}

void saveLog() {
	if (lastQueryFrom == -1) {
		cPrintf(COL_EXIT, "\n尚未进行过查询！\n");
		return;
	}

	FILE* fp = NULL;
	errno_t err = fopen_s(&fp, LOG_FILE, "a");
	if (err != 0 || fp == NULL) {
		perror("写日志失败");
		return;
	}

	time_t now; struct tm tm_info;
	char tb[64];
	time(&now);
	localtime_s(&tm_info, &now);
	strftime(tb, sizeof(tb), "%Y-%m-%d %H:%M:%S", &tm_info);

	fprintf(fp, "======================================================================\n");
	fprintf(fp, "查询时间: %s\n", tb);
	fprintf(fp, "查询模式: %s\n", profiles[current_mode].mode_name);
	fprintf(fp, "起点站: %s\n", lastQueryFromName);
	fprintf(fp, "终点站: %s\n", lastQueryToName);
	fprintf(fp, "途经站数量: %d\n", lastQueryViaCount);
	if (lastQueryViaCount > 0) {
		fprintf(fp, "途经站: ");
		for (int i = 0; i < lastQueryViaCount; i++) {
			fprintf(fp, "%s%s", lastQueryViaNames[i], i == lastQueryViaCount - 1 ? "\n" : " -> ");
		}
	}
	fprintf(fp, "-----------------------------------------------------------------------------------------------------------------\n");
	fprintf(fp, "%s", log_buffer);
	fprintf(fp, "======================================================================\n\n");

	fclose(fp);
	cPrintf(COL_INPUT, "\n已追加保存到 %s\n", LOG_FILE);
}

void showMenu() {
	time_t now; time(&now);
	struct tm tm_buf;
	localtime_s(&tm_buf, &now);
	char timeStr[30];
	strftime(timeStr, sizeof(timeStr), "%Y-%m-%d %H:%M:%S", &tm_buf);

	SetColor(COL_TITLE);
	printf("┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓\n");
	printf("┃         重庆轨道交通查询系统  m_884@qq.com          ┃\n");
	printf("┃         当前时间：%s               ┃\n", timeStr);
	printf("┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛\n");
	ResetColor();

	SetColor(COL_MENU);
	printf("┌──────────────────────────────┐\n");
	printf("│  1. 查询路线                 │\n");
	printf("│  2. 保存上次结果到日志       │\n");
	printf("│  3. 重复上次查询             │\n");
	printf("│  4. 切换查询模式             │\n");
	printf("│  5. 显示所有线路及换乘站     │\n");
	printf("│  6. 退出                     │\n");
	printf("└──────────────────────────────┘\n");
	ResetColor();

	cPrintf(COL_MENU, "当前模式：");
	cPrintf(COL_TRANS, "%s\n", profiles[current_mode].mode_name);
	cPrintf(COL_INPUT, "请选择（1-6）：>> ");
}

void switchMode() {
	cPrintf(COL_TITLE, "\n┌──────────────────────────────┐\n");
	cPrintf(COL_TITLE, "│        选择查询模式          │\n");
	cPrintf(COL_TITLE, "├──────────────────────────────┤\n");
	cPrintf(COL_MENU, "│  1. 极致少换乘               │\n");
	cPrintf(COL_MENU, "│  2. 时间最优先               │\n");
	cPrintf(COL_MENU, "│  3. 均衡舒适                 │\n");
	cPrintf(COL_TITLE, "└──────────────────────────────┘\n");
	cPrintf(COL_INPUT, "请选择模式（1-3）：>> ");

	int mode;
	if (scanf_s("%d", &mode) != 1 || mode < 1 || mode > 3) {
		discard_stdin();
		cPrintf(COL_EXIT, "\n无效选择！\n");
		return;
	}
	discard_stdin();

	current_mode = mode - 1;
	cPrintf(COL_ARRIVE, "\n已切换到：%s\n", profiles[current_mode].mode_name);
}

void listAllLines() {
	cPrintf(COL_TITLE, "\n---------- 所有线路及换乘站 ----------\n");
	for (int lid = 0; lid < line_count; lid++) {
		cPrintf(COL_MENU, "\n【%s】换乘站: ", lines[lid].line_name);
		int first = 1;
		for (int i = 0; i < station_count; i++) {
			if (!stations[i].is_transfer) continue;
			for (int j = 0; j < station_count; j++) {
				if (Connect[i][j] && (LineMask[i][j] & (1ULL << lid))) {
					cPrintf(COL_TRANS, "%s%s", first ? "" : "、", stations[i].station_name);
					first = 0;
					break;
				}
			}
		}
		if (first) cPrintf(COL_MENU, "无");
	}
	cPrintf(COL_MENU, "\n");
}

void choiceFunction() {
	while (1) {
		showMenu();
		int choice;
		if (scanf_s("%d", &choice) != 1) {
			choice = 0;
			discard_stdin();
		}
		else {
			discard_stdin();
		}

		switch (choice) {
		case 1:
			system("cls");
			routeQuery();
			cPrintf(COL_MENU, "\n按回车键返回菜单...");
			discard_stdin();
			system("cls");
			break;

		case 2:
			system("cls");
			saveLog();
			cPrintf(COL_MENU, "\n按回车键返回菜单...");
			discard_stdin();
			system("cls");
			break;

		case 3:
			system("cls");
			repeatLastQuery();
			cPrintf(COL_MENU, "\n按回车键返回菜单...");
			discard_stdin();
			system("cls");
			break;

		case 4:
			system("cls");
			switchMode();
			cPrintf(COL_MENU, "\n按回车键返回菜单...");
			discard_stdin();
			system("cls");
			break;

		case 5:
			system("cls");
			listAllLines();
			cPrintf(COL_MENU, "\n按回车键返回菜单...");
			discard_stdin();
			system("cls");
			break;

		case 6:
			system("cls");
			cPrintf(COL_TITLE, "\n感谢使用，再见！\n");
			return;

		default:
			system("cls");
			cPrintf(COL_EXIT, "\n输入无效，请重试！\n");
			cPrintf(COL_MENU, "\n按回车键返回菜单...");
			discard_stdin();
			system("cls");
			break;
		}
	}
}

void loadData() {
	FILE* fp = NULL;
	errno_t err = fopen_s(&fp, "subway.txt", "r");
	if (err != 0 || fp == NULL) {
		cPrintf(COL_EXIT, "错误：无法打开数据文件 'subway.txt'！\n");
		exit(1);
	}

	int total_lines;
	if (fscanf_s(fp, "%d", &total_lines) != 1 || total_lines <= 0) {
		cPrintf(COL_EXIT, "错误：无效的总线路数量！\n");
		fclose(fp);
		return;
	}

	// 消耗第一行后的换行符
	char buffer[2048];
	fgets(buffer, sizeof(buffer), fp);

	memset(stations, 0, sizeof(stations));
	memset(lines, 0, sizeof(lines));
	memset(Connect, 0, sizeof(Connect));
	memset(LineMask, 0, sizeof(LineMask));
	station_count = 0;
	line_count = 0;

	cPrintf(COL_MENU, "正在加载数据，共 %d 条线路...\n", total_lines);

	for (int l = 0; l < total_lines && l < MAXL; l++) {
		char lineName[MAXS];
		int stationNum, isFast, isSuburban;

		// 读取线路信息：名称 站点数 是否快线 是否市郊
		if (fscanf_s(fp, "%s %d %d %d",
			lineName, (unsigned)sizeof(lineName),
			&stationNum, &isFast, &isSuburban) != 4) {
			cPrintf(COL_EXIT, "第 %d 行线路信息格式错误\n", l + 2);
			fgets(buffer, sizeof(buffer), fp); // 跳过错误行
			continue;
		}

		if (stationNum <= 0) {
			cPrintf(COL_EXIT, "第 %d 行站点数量无效: %d\n", l + 2, stationNum);
			continue;
		}

		int lineId = get_line_id_by_name(lineName);
		if (lineId < 0) {
			cPrintf(COL_EXIT, "  警告：线路数量上限，跳过 %s\n", lineName);
			// 跳过该线路的站点
			for (int i = 0; i < stationNum; i++) {
				fgets(buffer, sizeof(buffer), fp);
			}
			continue;
		}

		strcpy_s(lines[lineId].line_name, sizeof(lines[lineId].line_name), lineName);
		lines[lineId].line_id = lineId;
		lines[lineId].station_count = stationNum;
		lines[lineId].is_fast = (isFast == 1);
		lines[lineId].is_surban = (isSuburban == 1);

		cPrintf(COL_VIA, "  加载线路: %s (%d站, %s, %s)\n",
			lineName, stationNum,
			lines[lineId].is_fast ? "快线" : "普通",
			lines[lineId].is_surban ? "市郊" : "市区");

		int prevStationId = -1;
		for (int i = 0; i < stationNum && i < MAXN; i++) {
			char stationName[MAXS];
			int attr;

			if (fscanf_s(fp, "%s %d",
				stationName, (unsigned)sizeof(stationName),
				&attr) != 2) {
				cPrintf(COL_EXIT, "  站点格式错误\n");
				break;
			}

			int stationId = get_station_id_by_name(stationName);
			if (stationId < 0) {
				cPrintf(COL_EXIT, "  站点数量上限，跳过 %s\n", stationName);
				continue;
			}

			if (attr & 1) stations[stationId].is_transfer = true;
			if (attr & 2) stations[stationId].is_great = true;

			lines[lineId].stations[i] = stationId;

			int lineIdx = 0;
			while (lineIdx < MAXL && stations[stationId].line[lineIdx] != 0) lineIdx++;
			if (lineIdx < MAXL) stations[stationId].line[lineIdx] = lineId;

			if (prevStationId != -1) {
				Connect[prevStationId][stationId] = Connect[stationId][prevStationId] = 1;
				unsigned long long mask = 1ULL << lineId;
				LineMask[prevStationId][stationId] |= mask;
				LineMask[stationId][prevStationId] |= mask;
			}

			prevStationId = stationId;
		}
	}

	// 自动检测换乘站
	for (int i = 0; i < station_count; i++) {
		int lineCountForStation = 0;
		for (int j = 0; j < line_count; j++) {
			for (int k = 0; k < lines[j].station_count; k++) {
				if (lines[j].stations[k] == i) {
					lineCountForStation++;
					break;
				}
			}
		}
		if (lineCountForStation > 1) {
			stations[i].is_transfer = true;
		}
	}

	fclose(fp);

	int transferCount = 0, greatCount = 0, fastCount = 0, surbanCount = 0;
	for (int i = 0; i < station_count; i++) {
		if (stations[i].is_transfer) transferCount++;
		if (stations[i].is_great) greatCount++;
	}
	for (int i = 0; i < line_count; i++) {
		if (lines[i].is_fast) fastCount++;
		if (lines[i].is_surban) surbanCount++;
	}

	cPrintf(COL_MENU, "\n数据加载完成！共 %d 个站点，%d 条线路\n", station_count, line_count);
	cPrintf(COL_MENU, "其中换乘站 %d 个，大站 %d 个\n", transferCount, greatCount);
	cPrintf(COL_MENU, "快速线路 %d 条，市郊铁路 %d 条\n", fastCount, surbanCount);

	Sleep(1500);
}

int main() {
	loadData();
	system("cls");
	choiceFunction();
	return 0;
}