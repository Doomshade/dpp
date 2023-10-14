/*
 * 
 * include do refint_asm, deklaruje ROZSIRENY vnitrni jazyk PL/0
 *
 * chybova hlaseni interpretu
 */

#define PC_MIMO_ROZSAH          1
#define PRETECENI               2
#define PODTECENI               3
#define DELENI_NULOU            4
#define PODTECENI_BAZE          5
#define NEZNAMA_INSTRUKCE       6
#define	MALO_PAMETI				7
#define	CHYBA_UVOLNENI_PAMETI	8
#define CHYBA_ADRESOVANI		9

char chyba_interpretace[10][50] = 
{ "OK", 
  "citac instrukci (PC) mimo rozsah", 
  "preteceni zasobniku", 
  "podteceni zasobniku", 
  "deleni nulou", 
  "chybne vyhledani baze",
  "neznama instrukce",
  "malo pameti pro alokaci",
  "chyba uvolneni pameti",
  "chyba adresace"};

/*
 * instrukce a klicova slova
 */

#define POCET_KLIC_SLOV         20
#define MAX_PISMEN_INSTRUKCE	6  /* pozor - vztahuje se i na instrukce 
				      debuggeru! */
typedef char KLICSLOVO[MAX_PISMEN_INSTRUKCE+1];

#define MIN_PARAMETRU_INSTRUKCE	2
#define MAX_PARAMETRU_INSTRUKCE	2
typedef int INSTRUKCE[2+MAX_PARAMETRU_INSTRUKCE]; /* [0] = pocet parametru, [1] = instrukce, [2], ... parametry */

/* tabulka klicovych slov, musi byt velkymi pismeny */
KLICSLOVO klicova_slova[POCET_KLIC_SLOV] = 
{"LIT  ", "OPR  ", "LOD  ", "STO  ", "CAL  ", 
 "RET  ", "INT  ", "JMP  ", "JMC  ", 
 "REA  ", "WRI  ",                                /* read <integer>, write <ascii> */
 "OPF  ", "RTI  ", "ITR  ",                       /* operace ve floatu; float -> integer; integer -> float */
 "NEW  ", "DEL  ",                                /* alokace a dealokace na halde */
 "LDA  ", "STA  ",								  /* load a store na zadanou absolutni adresu */ 
 "PLD  ", "PST  "                                 /* load a store na zadanou adresu L, A */ 
};

#define LIT   0		/* LIT ? konst   -> na vrchol zasobniku konst */
#define OPR   1     /* OPR ? funkce  -> modifikace zasobniku */
#define LOD   2     /* LOD L A       -> na vrchol zasobniku data z (L, A) */
#define STO   3		/* STO L A		 -> data z vrcholu zasobniku na (L, A) */
#define CAL   4		/* CAL L A       -> skok na A s hladinou zanoreni L */
#define RET   5		/* RET ? ?		 -> navrat z podprogramu */
#define INT   6		/* INT ? konst   -> zvedne vrchol zasobniku o konst */
#define JMP   7		/* JMP ? A       -> skok na A */
#define JMC   8     /* JMC ? A       -> skok podle hodnoty na vrcholu zasobniku */
#define REA   9     /* REA ? ?       -> na vrchol zasobniku nactene cislo */
#define WRI  10     /* WRI ? ?       -> vypis ascii znaku podle vrcholu zasobniku */
#define OPF  11     /* OPF ? funkce  -> modifikace zasobniku s plovoucimi hodnotami */
#define RTI  12     /* RTI ? ?       -> ze 2 hodnot (double) na zasobniku se udela 1 (int) */
#define ITR  13     /* ITR ? ?       -> z 1 hodnoty (int) na zasobniku se udelaji 2 (double) */
#define NEW  14     /* NEW ? ?       -> alokace 1 bunky pameti, na zasobnik jeji adresa */
#define DEL  15     /* DEL ? ?       -> dealokace 1 bunky pameti, jeji adresa na vrcholu zasobniku */
#define LDA  16		/* LDA ? ?		 -> na vrchol zasobniku data z adresy uvedene na vrcholu zasobniku */
#define STA  17     /* STA ? ?       -> na zasobniku hodnota, adresa -> ulozeni hodnoty na adresu */
#define PLD  18     /* PLD ? ?       -> na zasobniku L, A -> na vrchol hodnota z (L, A) */
#define PST  19     /* PST ? ?       -> na zasobnkku X, L, A -> na adresu (L, A) se ulozi X */

#define NEG   1
#define ADD   2
#define SUB   3
#define MUL   4
#define DIV   5
#define MOD   6
#define ODD   7
#define EQ    8
#define NE    9
#define LT   10
#define GE   11
#define GT   12
#define LE   13

