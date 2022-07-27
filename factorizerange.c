#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>
#include <sys/timeb.h>

#ifdef BOINC
    #include "boinc_api.h"
#endif

#ifdef __linux__
	#include <sys/utsname.h>
#endif

#define PROGRAM_NAME "Factorize Range"
#define VERSION "1.00"
#define YEARS "2022"
#define AUTHOR "Alexander Belogourov aka x3mEn"

#ifdef _WIN64
    const char* OS = "Windows 64-bit";
#elif _WIN32
    const char* OS = "Windows 32-bit";
#elif __APPLE__ || __MACH__
    const char* OS = "Mac OS X";
#elif __FreeBSD__
    const char* OS = "FreeBSD";
#else
    const char* OS = "Other";
#endif

// almost - режим пошуку майже ідеальних кубоїдів
int almost = 0;
// progress - режим із відображенням прогресу
int progress = 0;
// quiet - подавити вивід на stdout
int quiet = 0;
// output - відправити stdout у файл out_%
int output = 0;
// report - створити файл із статистикою задачі rep_%
int report = 0;
// backward - пошук у зворотньому напрямку
int backward = 0;
// skip - вважати такими, що виконані, завдання, для яких є out і немає chk
int skip = 0;
// debug - режим із відображенням факторизації та декомпозицій
int debug = 0;
uint32_t debug_step = 1;
// verbose - режим із виводом результату в stderr
int verbose = 0;
uint32_t verbose_step = 1;

// check sum
uint64_t check_sum = 0;
//uint64_t loopCnt = 0;

#define max(a,b) ((a) > (b) ? a : b)
#define min(a,b) ((a) < (b) ? a : b)
#define sign(x) (x > 0 ? 1 : (x == 0 ? 0 : -1))

#ifndef HAVE_BZERO
    #define bzero(ptr,n) \
    memset(ptr, 0, n)
#endif //HAVE_BZERO

#define xchgu64(a,b) \
do {uint64_t c = *a; *a = *b; *b = c;} while (0)

#define xchgu128(a,b) \
do {__uint128_t c = *a; *a = *b; *b = c;} while (0)

// 6542 простих, менших за 2^16 = 65536
#define SMALL_PRIMES_CNT 6542
uint32_t SmallPrimes[SMALL_PRIMES_CNT];

uint32_t * Primes = NULL;
uint32_t primes_size = 0;

const int step = 2;
const uint64_t minA = 3;
const uint64_t maxA = (int64_t)((INT64_MAX - 1) / step - 1) * 2 + 1;

struct timeb starttime, endtime;
FILE * fout, * frep, * fchk;

uint32_t block_size = 100000;
typedef struct {uint64_t number; uint8_t divs;} TBlock;
TBlock * Block = NULL;
uint32_t bSize = 0;

// Число 16294579238595022365 = 3*5*7*11*13*17*19*23*29*31*37*41*43*47
// має найбільшу кількість різних непарних дільників — 14, серед чисел менштх за 2^63.
// Тому для зберігання факторизації будь-якого числа, що нас цікавлять, достатньо масиву з 14 елементів
#define MAX_DIVISORS_CNT 14

uint32_t max_squares_cnt = 0;

typedef struct { uint64_t prime; uint8_t power ;} TDivisor;
TDivisor * Divisors[MAX_DIVISORS_CNT];

uint32_t
     pcCnt = 0 // кількість ідеальних кубоїдів
    ,bcCnt = 0 // кількість майже ідеальних кубоїдів з нецілою просторовою діагоналлю
    ,cnCnt = 0 // кількість кандидатів, що потрапили на перевірку
    ,toCnt = 0; // загальна кількість знайдених кубоїдів

uint64_t ini, fin, cur, task_ini, task_fin;
char repfname[256] = "rep", outfname[256] = "out", chkfname[256] = "chk";

static __inline__ uint64_t string_to_u64(const char * s) {
  uint64_t i;
  char c ;
  int scanned = sscanf(s, "%" SCNu64 "%c", &i, &c);
  if (scanned == 1) return i;
  if (scanned > 1) {
    // TBD about extra data found
    return i;
    }
  // TBD failed to scan;
  return 0;
}

void factorize_range(void)
{
    uint32_t i, j, k, l, MaxFactor = rintl(sqrtl(Block[(bSize)-1].number));
    uint64_t d, n;
    n = Block[0].number;
    for (j = 0; j < primes_size && Primes[j] <= MaxFactor; j++) {
        d = Primes[j];
        k = n % d;
        if (k) {
            if (n > d)
                k = d - ((n - d)/step) % d;
            else
                k = ((d - n)/step) % d;
        }
        for (i = k; i < bSize; i += d){
            if (!(Block[i].number % d)) {
                Divisors[Block[i].divs][i].prime = d;
                do {
                    Block[i].number /= d;
                    Divisors[Block[i].divs][i].power++;
                } while (!(Block[i].number % d));
                Block[i].divs++;
            }
        }
    }
    for (i = 0; i < bSize; i++) {
        k = Block[i].divs;
        if (Block[i].number > 1) {
            Divisors[Block[i].divs][i].prime = Block[i].number;
            Divisors[Block[i].divs++][i].power++;
        }
        for (j = 0; j < k; j++)
            for (l = 0; l < Divisors[j][i].power; l++)
                Block[i].number *= Divisors[j][i].prime;
    }
}

void save_checkpoint(uint64_t pos)
{
    fchk = fopen(chkfname, "w");
    if(fchk == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    struct timeb curtime;
    ftime(&curtime);
    uint64_t dif = (curtime.time - starttime.time) * 1000 + (curtime.millitm - starttime.millitm);
    fprintf(fchk,  "%" PRIu64
                  ",%" PRIu64
                  ",%" PRIu64
                  ",%" PRIu64
                  ",%d,%" PRIu64
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                ,ini
                ,fin
                ,pos
                ,check_sum
                ,backward
                ,dif
                ,cnCnt
                ,pcCnt
                ,bcCnt
           );
    fflush(fchk);
    fclose(fchk);
#if defined BOINC
	boinc_checkpoint_completed();
#endif
}

int read_checkpoint(void)
{
    fchk = fopen(chkfname, "r");
    if(fchk == NULL)
        return (EXIT_FAILURE);
    char c;
    uint64_t dif;
    int scanned = fscanf(fchk, "%" SCNu64
                              ",%" SCNu64
                              ",%" SCNu64
                              ",%" SCNu64
                              ",%d,%" SCNu64
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%c"
                              , &ini
                              , &fin
                              , &cur
                              , &check_sum
                              , &backward
                              , &dif
                              , &cnCnt
                              , &pcCnt
                              , &bcCnt
                              , &c);
    fclose(fchk);
    if (scanned != 13) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    if (!cur) return 1;
        else cur = ((cur / step) + 1) * step + 1;
    starttime.time -= dif / 1000;
    long int millisec = (dif % 1000);
    if (starttime.millitm < millisec) {
        starttime.millitm += 1000 - millisec;
        starttime.time--;
    } else starttime.millitm -= millisec;
    toCnt = pcCnt + bcCnt;
    return 0;
}

void free_primes(void)
{
    free(Primes);
}

void init_primes(void)
{
    uint32_t sq = ceil(sqrtl(fin)), cb = ceil(sqrtl(sqrtf(fin)));
    uint32_t sSize = max(ceil((float)sq / 128), SMALL_PRIMES_CNT);
    uint32_t i, j;
    uint64_t * sieve;
    sieve = (uint64_t*) calloc (sSize, sizeof(uint64_t));
    if (sieve == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    sieve[0] = 1;
    for (i = 1; i < sSize; i++) sieve[i] = 0;
    for (i = 3; i <= cb; i += 2) {
        for (j = 3*i; j <= sq; j += 2*i) {
            sieve[j >> 7] |= ((uint64_t)1 << ((j >> 1)&63));
        }
    }
    SmallPrimes[0] = 2;
    j = 1;
    for (i = 3; j < SMALL_PRIMES_CNT ; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63))))
            SmallPrimes[j++] = i;
    }
    primes_size = 0;
    for (i = 3; i <= sq; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63)))) {
            primes_size++;
        }
    }
    Primes = (uint32_t*) malloc (sizeof(uint32_t)*primes_size);
    if (Primes == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    primes_size = 0;
    for (i = 3; i <= sq; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63)))) {
            Primes[primes_size++] = i;
        }
    }
    free(sieve);
}

void free_block(void)
{
    if (Block != NULL)
        for (uint8_t j = 0; j < MAX_DIVISORS_CNT; j++)
            free(Divisors[j]);
    free(Block);
}

void init_block(uint32_t size)
{
    free_block();
    bSize = size;
    Block = (TBlock *) calloc(size, sizeof(TBlock));
    if (Block == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    for (uint8_t j = 0; j < MAX_DIVISORS_CNT; j++) {
        Divisors[j] = (TDivisor *) calloc(size, sizeof(TDivisor));
        if (Divisors[j] == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
    }

    uint64_t n = cur;
    for (uint32_t i = 0; i < size; i++) {
        Block[i].number = n;
        n += step;
    }
}

int init_task(void)
{
    if (ini > fin) return 1;
    if (ini < minA) ini = minA;
    if (fin > maxA) fin = maxA;
    ini = (uint64_t)((ini + step - 2) / step) * step + 1;
    fin = (uint64_t)((fin - 1) / step) * step + 1;
    cur = ini;
    return 0;
}

static __inline__ int next_task(void)
{
    if (maxA - step >= cur) cur += step;
    else return 6;
    if (cur > fin) return 7;
    return 0;
}

#define PBSTR "========================================================================"
#define PBWIDTH 45
#define SCRWIDTH 80
void do_progress( double percentage )
{
    int val = (int) (percentage);
    int lpad = (int) (percentage  * (val==100?SCRWIDTH:PBWIDTH) / 100);
    int rpad = (val==100?SCRWIDTH:PBWIDTH) - lpad;
    //fill progress bar with spaces
    fprintf(stderr, "\r%3d%% [%.*s%*s]", val, lpad, PBSTR, rpad, "");
}

void print_factors(uint32_t i)
{
    uint64_t n = Block[i].number;
    char divisorsStr[256], pclose[2], popen[2];
//    fprintf(stderr, "------------------------------------------------------------------------------\n");
//    if (Block[i].divs == 1 && Divisors[0][i].power == 1)
//        fprintf(stderr, "%" PRIu64 " is a prime number\n",n);
//    else
//        if (Block[i].divs > 1) fprintf(stderr, "%" PRIu64 " has %i different divisors\n",n,Block[i].divs);
//        else fprintf(stderr, "%" PRIu64 " is a power of prime\n",n);
    bzero(divisorsStr, 256);
    for (int j=0; j < Block[i].divs; j++) {
        if (j > 0) sprintf(divisorsStr, "%s * ", divisorsStr);
        sprintf(divisorsStr, "%s%" PRIu64, divisorsStr, Divisors[j][i].prime);
        if (Divisors[j][i].power > 1) sprintf(divisorsStr, "%s^%i", divisorsStr, Divisors[j][i].power);
    }
    fprintf(stderr, "%" PRIu64 " = %s\n",n,divisorsStr);
}

void print_usage(void)
{
#ifdef _WIN32
	char pref[3] = "";
#elif __linux__ || unix || __unix__ || __unix
	char pref[3] = "./";
#endif // __linux__
    fprintf(stderr, "Usage: %spcuboid <low> <high> [switches]\n", pref);
    fprintf(stderr, "\t<low>\t\tlower border\n");
    fprintf(stderr, "\t<high>\t\thigher border\n");
    fprintf(stderr, "The following switches are accepted:\n");
    fprintf(stderr, "\t-a\t\tsearch for almost-perfect cuboids\n");
    fprintf(stderr, "\t-q\t\tsuppress output to stdout\n");
    fprintf(stderr, "\t-p\t\tdisplay progress bar\n");
    fprintf(stderr, "\t-o\t\twrite results to output file\n");
    fprintf(stderr, "\t-r\t\twrite task stat to report file\n");
    fprintf(stderr, "\t-s\t\tskip task if output file exists\n");
    fprintf(stderr, "\t-f [s]\t\tfactoring block size (default value: %" PRIu32 ")\n", block_size);
    fprintf(stderr, "\t-d [m]\t\tdebug mode\n\t\t\tdisplay (every [m]) factorizations\n");
    fprintf(stderr, "\t-v [n]\t\tverbose mode\n\t\t\tdisplay (every [n]) found results\n");
}

int main(int argc, char** argv)
{
#if defined BOINC
	boinc_init();
#endif

#ifdef _WIN32
#elif __linux__ || unix || __unix__ || __unix
	char OS[256];
	struct utsname name;
	if(uname(&name)) exit(EXIT_FAILURE);
	sprintf(OS, "%s %s", name.sysname, name.release);
#endif // __linux__
    fprintf(stderr, "%s %s (%s)\nCopyright %s, %s\n\n", PROGRAM_NAME, VERSION, OS, YEARS, AUTHOR);
    if (argc < 3) {
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    task_ini = ini = string_to_u64(argv[1]);
    task_fin = fin = string_to_u64(argv[2]);
    if (!ini || !fin) {
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i],"-a")) {almost = 1; continue;}
        if (!strcmp(argv[i],"-q")) {quiet = 1; continue;}
        if (!strcmp(argv[i],"-p")) {progress = 1; continue;}
        if (!strcmp(argv[i],"-o")) {output = 1; continue;}
        if (!strcmp(argv[i],"-r")) {report = 1; continue;}
        if (!strcmp(argv[i],"-s")) {skip = 1; continue;}
        if (!strcmp(argv[i],"-f")) {continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-f")) {block_size = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-d")) {debug = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-d")) {debug_step = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-v")) {verbose = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-v")) {verbose_step = string_to_u64(argv[i]); continue;}
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    ftime(&starttime);

    time_t timer;
    char curdatetime[26];
    struct tm* tm_info;
    time(&timer);
    tm_info = localtime(&timer);
    strftime(curdatetime, 26, "%d.%m.%Y %H:%M:%S", tm_info);

#ifndef BOINC
    sprintf(repfname, "rep_%019" PRIu64 "_%019" PRIu64, task_ini, task_fin);
    sprintf(outfname, "out_%019" PRIu64 "_%019" PRIu64, task_ini, task_fin);
    sprintf(chkfname, "chk_%019" PRIu64 "_%019" PRIu64, task_ini, task_fin);
#endif

    int ErrorCode, CheckPointCode;
    ErrorCode = CheckPointCode = read_checkpoint();
    if (ErrorCode) ErrorCode = init_task();
    if (ErrorCode) return ErrorCode;

    uint64_t total = fin >= ini ? (uint64_t)((fin - ini) / step) + 1 : 0;

    uint64_t state = 0, cubCnt = 0, block_elem = (block_size - 1) * step;

    fout = fopen(outfname, "r");
    if (skip && fout != NULL && CheckPointCode) {
        fclose(fout);
#ifdef BOINC
	boinc_finish(EXIT_SUCCESS);
#endif
        exit (EXIT_SUCCESS);
    }
    if (output) {
        if (!CheckPointCode && fout == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        if (CheckPointCode) {
            fout = fopen(outfname, "w");
        } else {
            fout = fopen(outfname, "a");
        }
        if (fout == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
    }

    fprintf(stderr, "Command line parameters :");
    for (int i = 1; i < argc; i++)
        fprintf(stderr, " %s", argv[i]);
    fprintf(stderr, "\n");
    fprintf(stderr, "Range                   : from %" PRIu64 " to %" PRIu64 " step %i\n", ini, fin, step);
    fprintf(stderr, "Total amount of Numbers : %" PRIu64 "\n", total);
    fprintf(stderr, "Factoring Block Size    : %" PRIu32 "\n", block_size);
    fprintf(stderr, "Start time              : %s\n", curdatetime);
#ifdef BOINC
    fprintf(stderr, "\n");
#endif

    init_primes();

    int cpcnt, ctpcnt = 0;
    float cstep = 0.01;
    int fpcnt, ftpcnt = 0;
    float fstep = 0.0001;

    if (progress)
        do_progress(ctpcnt);
#ifdef BOINC
    boinc_fraction_done(0);
#endif

    while (ini <= cur && cur <= fin) {
        uint32_t bs = (fin - cur < block_elem ? fin - cur : block_elem) / step + 1;
        init_block(bs);
        factorize_range();
        for (uint32_t i = 0; i < bSize; i++) {
            cnCnt++;
            if (debug && !progress && !(cnCnt % debug_step))
                print_factors(i);
            state = (Block[i].number - ini) / step + 1;
            cpcnt = (int)((double)state / total / cstep);
            if (ctpcnt != cpcnt || cubCnt < toCnt) {
                ctpcnt = cpcnt;
                cubCnt = toCnt;
                if (progress)
                    do_progress((double)state / total * 100);
                //save_checkpoint(Block[i].number + 1);
                if (output) fflush(fout);
                fflush(stdout);
            }
        }
        fpcnt = (int)((double)state / total / fstep);
        if (ftpcnt != fpcnt) {
            ftpcnt = fpcnt;
#ifdef BOINC
            boinc_fraction_done((double)state / total);
#endif
        }
        cur += bSize * step;
    };

    if (output) fclose(fout);
    remove(chkfname);

    ftime(&endtime);
    uint64_t dif = (endtime.time - starttime.time) * 1000 + (endtime.millitm - starttime.millitm);

#ifndef BOINC
    fprintf(stderr, "\n");
#endif
    fprintf(stderr, "Elapsed time            : %02d:%02d:%02d.%03d\n", (unsigned char)(dif/60/60/1000), (unsigned char)((dif/60/1000)%60), (unsigned char)((dif/1000)%60), (unsigned char)(dif%1000));
//    fprintf(stderr, "Loop cnt                : %" PRIu64 "\n", loopCnt);
//    fprintf(stderr, "Check sum               : %" PRIu64 "\n", check_sum);
    fprintf(stderr, "Candidates              : %" PRIu32 "\n", cnCnt);
    fprintf(stderr, "Perfect Cuboids         : %" PRIu32 "\n", pcCnt);
    fprintf(stderr, "Body Cuboids            : %" PRIu32 "\n", bcCnt);
    if (report) {
        frep = fopen(repfname, "w");
        if(frep == NULL) {
            perror("Failed to open rep file");
#ifdef BOINC
			boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        fprintf(frep,  "%" PRIu64
                      ",%" PRIu64
#ifdef BOINC
                      ",%" PRIu64
#endif
#ifndef BOINC
                      ",%s,%s,%02d:%02d:%02d.%03d"
#endif
                      ",%" PRIu64
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      "\n"
                    ,task_ini
                    ,task_fin
#ifdef BOINC
                    ,check_sum
#endif
#ifndef BOINC
                    ,VERSION
                    ,OS
                    ,(unsigned char)(dif/60/60/1000), (unsigned char)((dif/60/1000)%60), (unsigned char)((dif/1000)%60), (unsigned char)(dif%1000)
#endif
                    ,total
                    ,cnCnt
                    ,pcCnt
                    ,bcCnt
               );
        fclose(frep);
    }
    free_block();
    free_primes();
#ifdef BOINC
    boinc_finish(EXIT_SUCCESS);
#endif
    return (EXIT_SUCCESS);
}
