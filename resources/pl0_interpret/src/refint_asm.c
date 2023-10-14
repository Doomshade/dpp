/*
 * referencni interpret "strojoveho jazyka"
 * s jednoduchym assemblerem
 */

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>

/*
 * velikost pameti kodu a pameti dat virtualniho pocitace
 */

#define PAMET_KODU	2000
#define PAMET_DAT	2000



/*
 * navraty z funkci (zejmena) pro lexikalni analyzu
 */

#define CHYBA	1
#define OK	0



/*
 * definice instrukci PL/0
 */
#include "instrukce_pl0_ext.h"

/*
 * globalni promenne pro lexikalni analyzu
 */

int nacteny_znak;          /* nacteny a nezpracovany znak ze souboru */
int vysledek_nacteni;      /* vysledek posledniho nacitani slova */


/* 
 * promenne pro assembler a debugger
 */

#define MAX_DELKA_LABELU    20
#define LABEL_NENALEZEN     -1
#define LABEL_NEDEFINOVAN   -1
#define STD_POCET_LABELU   500
#define STD_NAHRAD_LABELU  500

/*
 * standardne predpokladame vstup s absolutnimi adresami
 * nulova hodnota indikuje vstup s labely (tj. s relativnimi adresami)
 */
int absolutni_adresovani = 1;


/*
 * pri nalezeni labelu na vstupu se tento poznamena do globalniho
 * seznamu
 */
typedef struct {
	char jmeno[MAX_DELKA_LABELU+1]; /* label ze vstupniho souboru */
	int hodnota;                    /* na jakou adresu ukazuje */
} T_LABEL;
T_LABEL *label;
int pocet_labelu;      /* aktualni pocet nalezenych labelu */
int max_pocet_labelu;  /* delka pole label */

/*
 * jakmile se najde label v parametru instrukce, tato instrukce
 * se zaznamena a po nacteni celeho vstupu se vsechny labely
 * zameni za skutecne adresy
 */
typedef struct {
	int adresa;     /* ktera instrukce se ma modifikovat */
	int parametr;   /* ktery parametr */
	int label;      /* ukazatel do pole label */
} T_NAHRAD_LABEL;
T_NAHRAD_LABEL* nahrad_label;
int pocet_nahrad_labelu;  /* aktualni pocet prikazu nahrazeni */
int max_nahrad_labelu;    /* delka pole nahrad_label */


/*
 * jakmile se narazi na pozadavek debug vypisu, tento se 
 * poznamena do globalniho seznamu
 */
#define STD_DEBUG_PRIKAZU     500
typedef int T_DEBUG_PRIKAZ[3]; /* prikaz parametr1 parametr2 */
T_DEBUG_PRIKAZ *debug_prikazy; /* pole debug prikazu */
int pocet_debug_prikazu,       /* aktualni pocet prikazu v debug_prikazy */
    max_debug_prikazu;         /* delka pole debug_prikazy */

#define STD_DEBUG_ECHO_PRIKAZU	500
char* debug_echo_prikazy[STD_DEBUG_ECHO_PRIKAZU];
int pocet_debug_echo_prikazu;

/* 
 * ke kazde instrukci si drzime info o tom, ktere debugprikazy
 * se k ni vazou
 */
#define BEZ_DEBUGINFA          -1
int instr_debug_prikazy[PAMET_KODU][2];  /* 1. prikaz, posledni prikaz */


/*
 * pri debugvypisech se toto vypise na kazkou radku
 */
const char *debug_prefix = "          debug>  ";

#define DEBUG_NIC                 -1  /* init u instr_debug_prikazy */
#define DEBUG_VYPIS_REGISTRY       1
#define DEBUG_VYPIS_ZASOBNIK       2
#define DEBUG_VYPIS_AKT_ZAZNAM     3
#define DEBUG_VYPIS_ZASOBNIK_OD_DO 4
#define DEBUG_VYPIS_ZASOBNIK_N     5
#define DEBUG_ECHO				   6

#define DEBUG_POCET_KLICSLOV       7
KLICSLOVO debug_klicova_slova[DEBUG_POCET_KLICSLOV] =
{"------", "REGS  ", "STK   ", "STKA  ", "STKRG ", "STKN  ", "ECHO  "};



/*
 * globalni promenne pro rizeni behu interpretu
 */
int beh_trasovani = 0;        /* trasovani behu programu */
int beh_interpretuj_kod = 1;  /* ma se interpretovat kod? */
int beh_vypis_kod = 1;        /* ma se vypsat nacteny kod? */
int beh_debug = 1;            /* ma se vypisovat debuginfo? */
int beh_sto = 1;              /* ma se vypisovat vysledek prirazeni?*/

char *napoveda_programu = 
"REFINT: referencni interpret PL/0\n"
"Pouziti:\n"
"refint <parametr1> <parametr2> ...\n"
"parametr muze byt jmeno souboru nebo +/-:\n"
"a: +a = vstupni program ma absolutni adresovani, -a = vstupni program ma adresovani reseno navestimi\n"
"l: po nacteni programu se tento vypise s absolutnimi adresami\n"
"i: po nacteni se spusti interpret kodu\n"
"t: interpret vypisuje prave provadenou instrukci\n"
"s: interpret indikuje prirazeni vypisem hodnoty\n"
"d: interpret vypisuje ladici (debug) vystupy\n"
"h: vypise tuto napovedu\n"
"jmeno souboru se musi zadat pouze jedno nebo zadne; v takovem pripade\n"
"se bude vstup brat z klavesnice\n"
"Standardni nastaveni prepinacu je +a +l +i -t +d +s\n";


/*
 * uzivatelsky zajimave funkce
 */

/*
 * nacti kod
 * do pameti kodu nacte kod
 * (in)  file: soubor, ze ktereho se ma cist vstup
 * (out) kod: pamet kodu, musi byt predem alokovana
 * (out) delka_kodu: pocet nactenych instrukci
 * navrat: OK nebo CHYBA
 */
int nacti_kod(FILE *file, INSTRUKCE *kod, int *delka_kodu);

/*
 * podle nejlepsiho vedomi a svedomi prekontroluje spravnost instrukce
 * (minimalne spravny pocet parametru)
 */
int zkontroluj_instrukci(INSTRUKCE instrukce);

/*
 * vypis_kod
 * vypise kod od adresy start na stdout
 * (in) kod: pamet kodu
 * (in) start: pocatecni adresa kodu
 * (in) delka_kodu: pocet vypisovanych instrukci
 */
void vypis_kod(INSTRUKCE *kod, int start, int delka_kodu);

/*
 * interpret
 * interpretuje kod z pameti kodu "kod" od adresy start
 * funkce si vytvari vlastni virtualni pocitac, tj. pamet dat i registry
 * (in)      kod: pamet kodu
 * (inout) start: jako vstup pocatecni adresa program counteru
 *                jako vystup adresa, kde interpret skoncil
 * navrat: chybove hlaseni interpretu
 */
int interpret(INSTRUKCE *kod, int *start);

/*
 * zpracuj_prikazovou_radku
 * pro zprehledneni kodu
 */
int zpracuj_prikazovou_radku(int argc, char **argv, FILE **fin);


/*
 * init_assembler a ukonci_assembler
 * nahodi  a shodi tabulky labelu
 */
void init_assembler(void);
void ukonci_assembler(void);
int  nahrad_labely(INSTRUKCE *pamet_kodu, int delka_kodu, 
		   int *pc, int *chybny_label);
void init_debugger(void);
void ukonci_debugger(void);

/*
 * MAIN
 *
 */
int main(int argc, char **argv)
{
 int delka_kodu;
 INSTRUKCE pamet_kodu[PAMET_KODU];
 int pc = 0, vysledek, chybny_label;
 FILE *fin = NULL;

 if (zpracuj_prikazovou_radku(argc, argv, &fin) != OK)
	 exit(CHYBA);
 if (fin == NULL) fin = stdin;

 if (absolutni_adresovani == 0) init_assembler();
 init_debugger();
 vysledek = nacti_kod(fin, pamet_kodu, &delka_kodu);
 if (fin != stdin) fclose(fin);


 if (vysledek != OK) exit(CHYBA);

 if (absolutni_adresovani == 0)
 {
	 vysledek = nahrad_labely(pamet_kodu, delka_kodu, &pc, &chybny_label);
	 if (vysledek != OK) 
	 {
		 fprintf(stderr, "Label %s na adrese %d nedefinovan.\n",
				 label[chybny_label].jmeno, pc);
		 vypis_kod(pamet_kodu, 0, delka_kodu);
		 exit(CHYBA);
	 }
 }

 if (beh_vypis_kod) vypis_kod(pamet_kodu, 0, delka_kodu);

 if (beh_interpretuj_kod &&
     (vysledek = interpret(pamet_kodu, &pc)) != OK
    )
 {
	 printf("chyba interpretace u instrukce %d: %s\n", 
			 pc, chyba_interpretace[vysledek]);
 }

 if (absolutni_adresovani == 0) ukonci_assembler();
 ukonci_debugger();
 return OK;
}


/*
 * zpracuj_prikazovou_radku
 * pro zprehledneni kodu
 */
int zpracuj_prikazovou_radku(int argc, char **argv, FILE **fin)
{
 int i;
 i = 1;
 while (i < argc)
 {
	 if (argv[i][0] == '-' || argv[i][0] == '+') 
		 switch (argv[i][1])
		 {
			  case 'a' : if (argv[i][0] == '-') absolutni_adresovani = 0;
				     else absolutni_adresovani = 1;
					 break;
	          case 't' : if (argv[i][0] == '-') beh_trasovani = 0;
				     else beh_trasovani = 1;
		             break;
			  case 'h' : printf("%s", napoveda_programu);
				     exit(0);
	          case 'i' : if (argv[i][0] == '-') beh_interpretuj_kod = 0;
				     else beh_interpretuj_kod = 1;
			     break;
	          case 'l' : if (argv[i][0] == '-') beh_vypis_kod = 0;
				     else beh_vypis_kod = 1;
			     break;
	          case 's' : if (argv[i][0] == '-') beh_sto = 0;
				     else beh_sto = 1;
			     break;
	          case 'd' : if (argv[i][0] == '-') beh_debug = 0;
				     else beh_debug = 1;
			     break;
		  default :  printf("Neznamy prepinac u instrukce %d.\n", i);
		             return CHYBA;
		 }
	 else
	 {
		 if (*fin != NULL)
		 {
			 printf("Parametr %d je jiz druhy nazev souboru.\n",
					 i);
			 return CHYBA;
		 }
		 *fin = fopen(argv[i], "r");
		 if (*fin == NULL)
		 {
			 printf("Chyba otvirani souboru %s.\n", argv[i]);
			 return CHYBA;
		 }
	 }
	 i++;
 }
 return OK;
}


/*
 * init_assembler
 * inicializace assembleru, de facto jen inicializace tabulek navesti
 */
void init_assembler(void)
{
    label = (T_LABEL*) malloc(STD_POCET_LABELU*sizeof(T_LABEL));
    if (label == NULL)
    {
      fprintf(stderr, "Chyba alokace pameti\n");
      exit(0);
    }
    pocet_labelu = 0;
    max_pocet_labelu = STD_POCET_LABELU;

    nahrad_label = (T_NAHRAD_LABEL*) malloc(STD_NAHRAD_LABELU*
	                                    sizeof(T_NAHRAD_LABEL));
    if (label == NULL)
    {
      fprintf(stderr, "Chyba alokace pameti\n");
      exit(0);
    }
    pocet_nahrad_labelu = 0;
    max_nahrad_labelu = STD_NAHRAD_LABELU;
}


/*
 * ukonci_assembler
 * ukonceni cinnosti assembleru, uvolneni pameti
 */
void ukonci_assembler(void)
{
  free(label);
  free(nahrad_label);
}
	

/*
 * init_debugger
 * inicializace debuggeru, tj. tabulek pro debuginfo
 */
void init_debugger(void)
{
	int i;

	debug_prikazy = (T_DEBUG_PRIKAZ*) malloc(STD_DEBUG_PRIKAZU *
	                                         sizeof(T_DEBUG_PRIKAZ));
	if (debug_prikazy == NULL)
	{
          fprintf(stderr, "Chyba alokace pameti\n");
          exit(0);
        }
	max_debug_prikazu = STD_DEBUG_PRIKAZU;
	pocet_debug_prikazu = 0;
	pocet_debug_echo_prikazu = 0;

	for (i=0; i<PAMET_KODU; i++)
		instr_debug_prikazy[i][0] =
		instr_debug_prikazy[i][1] = DEBUG_NIC;
}


/*
 * ukonci_debugger
 * ukonceni debuggeru, uvolneni pameti
 */
void ukonci_debugger(void)
{
	int i;
	free(debug_prikazy);

	for (i=0; i<pocet_debug_echo_prikazu; i++)
		free(debug_echo_prikazy[i]);
}





/*
 * NACITANI VSTUPU
 */

/* pomocna globalni promenna pro odkaz na vstupni soubor */
FILE *_vstupni_soubor;


/*
 * dalsi_znak
 * ze souboru nacte dalsi znak a ulozi do globalni promenne nacteny_znak
 */
void dalsi_znak()
{
  nacteny_znak = getc(_vstupni_soubor);
}


/*
 * preskoc_mezery
 * preskakuje mezery (0x20) a tabulatory (\t)
 */
void preskoc_mezery(void)
{
 while (nacteny_znak == ' ' ||
        nacteny_znak == '\t')
  dalsi_znak();
}


/*
 * dalsi_radek
 * preskoci mezery, tabulatory a jeden konec radku (WIN i UNIX)
 */
void dalsi_radek(void)
{
 int pn=0, p0a=0, p0d=0, nxt;
 while (nacteny_znak == '\t' || 
        nacteny_znak == ' ') dalsi_znak();
 while (1)
 {
	 nxt = 0;
	 if (nacteny_znak == '\n')
	 {
	         if (pn) return;
	            else { pn = 1; nxt = 1; }
	 }
         if (nacteny_znak == 0x0d) 
	 {
	         if (p0d) return;
	            else { p0d = 1; nxt = 1; }
	 }
	 if (nacteny_znak == 0x0a) 
	 {
	         if (p0a) return;
	            else { p0a = 1; nxt = 1; }
	 }
         if (nxt) dalsi_znak();
	    else return;
 }
}


/*
 * preskoc_zbytek_radku
 * preskoci vsechny znaky do konce radku (WIN i UNIX) vcetne
 */
void preskoc_zbytek_radku(void)
{
 int pn=0, p0a=0, p0d=0, nxt;
 while (nacteny_znak != '\n' && 
	nacteny_znak != 0x0d &&
        nacteny_znak != 0x0a) dalsi_znak();
 while (1)
 {
	 nxt = 0;
	 if (nacteny_znak == '\n')
	 {
	         if (pn) return;
	            else { pn = 1; nxt = 1; }
	 }
         if (nacteny_znak == 0x0d) 
	 {
	         if (p0d) return;
	            else { p0d = 1; nxt = 1; }
	 }
	 if (nacteny_znak == 0x0a) 
	 {
	         if (p0a) return;
	            else { p0a = 1; nxt = 1; }
	 }
         if (nxt) dalsi_znak();
	    else return;
 }
}


/*
 * nacte zbytek radku do retezce
 * (out): nacteny retezec
 */
int nacti_retez_do_konce_radku(char **retez)
{
 char tmp[1000];
 int i;

 i = 0;
 while (nacteny_znak != '\n' && 
	    nacteny_znak != 0x0d &&
        nacteny_znak != 0x0a) 
 {
     tmp[i] = nacteny_znak;
	 i++;
	 dalsi_znak();
 }
 tmp[i] = 0;
 i++;

 if ((*retez = (char*) malloc(i)) == NULL) return CHYBA;
 strncpy(*retez, tmp, i);
 (*retez)[i-1] = 0;

 return OK;
}



/*
 * nacti_cislo
 * nacte ze vstupu cele znamenkove cislo
 * (out) nactene_cislo: hodnota nacteneho cisla
 * navrat: OK nebo CHYBA
 *         nastavuje globalni promennou vysledek_nacteni
 */

/*
 * test, zna znak je first(cislo)
 * funkce nacti_cislo ji nevyuziva, ale vyuziva se jinde v programu
 */

int nacti_cislo_test(char znak)
{
	if (znak == '-' || ( znak >='0' && znak <= '9' )) return OK;
	else return CHYBA;
}



int nacti_cislo(int *nactene_cislo)
{
 int num = 0;
 int zaporne = 0;
 int precteno = 0;

 if (vysledek_nacteni != OK) return CHYBA;


 if (nacteny_znak == '-') 
  {
   zaporne = 1;
   dalsi_znak();
  }

 while (nacteny_znak >= '0' && nacteny_znak <= '9')
  {
   precteno++;
   num = num*10 + (nacteny_znak - '0');
   dalsi_znak();
  }

 if (zaporne) *nactene_cislo = -num;
 else *nactene_cislo = num;

 if (precteno == 0) 
  {
   vysledek_nacteni = CHYBA;
   return CHYBA;
  }

 else return OK;
}



/*
 * nacti_klic_slovo
 * nacte ze vstupu klicove slovo
 * (out) klic_slovo: poradove cislo nacteneho slova v tabulce klicova_slova
 * (out) retez: nacteny retezec, musi byt alokovany
 * (out) max_delka: maximalni delka klicoveho slova
 * navrat: OK nebo CHYBA
 *         nastavuje globalni promennou vysledek_nacteni
 */
int nacti_klic_slovo(int *klic_slovo, char *retez, 
		     KLICSLOVO *klicova_slova, int pocet_klic_slov,
		     int max_delka)
{
 int precteno = 0;
 int nalezene, i;

 if (vysledek_nacteni != OK) return CHYBA;
 if (max_delka < 1) return OK;  /* neni co nacitat => OK */

 /* prvni znak je pismeno nebo _ */
 if ((nacteny_znak >= 'A' && nacteny_znak <= 'Z') ||
     (nacteny_znak >= 'a' && nacteny_znak <= 'z') ||
      nacteny_znak == '_')
  {
   retez[precteno++] = nacteny_znak;
   dalsi_znak();
  }
 else
  {
   vysledek_nacteni = CHYBA;
   return CHYBA;
  }
 
 /* dalsi znaky jsou pismeno, cislo nebo _ */
 while ((nacteny_znak >= 'A' && nacteny_znak <= 'Z') ||
        (nacteny_znak >= 'a' && nacteny_znak <= 'z') ||
        (nacteny_znak >= '0' && nacteny_znak <= '9') ||
         nacteny_znak == '_')
  {
   /* je-li na vstupu delsi retezec, je urcite chybny */	  
   if (precteno >= max_delka)
    {
     vysledek_nacteni = CHYBA;
     return CHYBA;
    }

   retez[precteno++] = nacteny_znak;
   dalsi_znak();
  }

 retez[precteno++] = '\0';

 /* hledani v tabulce klicovych slov, vse se prevadi na velka pismena */
 for (nalezene = 0; nalezene < pocet_klic_slov; nalezene++)
  {
   /* porovnavame znak po znaku s klicovym slovem dokud to jde */	  
   i = 0;
   while (retez[i] != '\0' &&
          klicova_slova[nalezene][i] != '\0' &&
          toupper(retez[i]) == klicova_slova[nalezene][i]) i++;

   /* pokud se s porovnavanim skoncilo na \0 nebo na mezere, je to ono */
   if (retez[i] == '\0' &&
       (klicova_slova[nalezene][i] == '\0' ||
        klicova_slova[nalezene][i] == ' '))
    {
     *klic_slovo = nalezene;
     return OK;
    }
  }

 /* slovo nebylo rozpoznano */
 vysledek_nacteni = CHYBA;
 return CHYBA;
}



/*
 * nacti_label
 * nacte label; pokud tento existuje, vrati se jeho cislo
 * (out) cislo_labelu
 * (out) retez: vlastni nazev labelu prevedeny na velka pismena
 * navrat: OK nebo CHYBA
 * modifikuje promennou vysledek_nacteni
 */
int nacti_label(int *cislo_labelu, char *retez)
{
 int precteno = 0;
 int nalezene, i;

 *cislo_labelu = 0;
 retez[0] = '\0';

 if (vysledek_nacteni != OK) return CHYBA;

 /* prvni znak je @ */
 if (nacteny_znak == '@')
  {
   dalsi_znak();
  }
 else
  {
   vysledek_nacteni = CHYBA;
   return CHYBA;
  }
 
 /* dalsi znaky jsou pismeno, cislo nebo _ */
 while ((nacteny_znak >= 'A' && nacteny_znak <= 'Z') ||
        (nacteny_znak >= 'a' && nacteny_znak <= 'z') ||
        (nacteny_znak >= '0' && nacteny_znak <= '9') ||
         nacteny_znak == '_')
  {
   /* je-li na vstupu delsi retezec, je urcite chybny */	  
   if (precteno > MAX_DELKA_LABELU)
    {
     vysledek_nacteni = CHYBA;
     return CHYBA;
    }

   retez[precteno++] = toupper(nacteny_znak);
   dalsi_znak();
  }

 retez[precteno++] = '\0';

 /* hledani v tabulce labelu */
 for (nalezene = 0; nalezene < pocet_labelu; nalezene++)
  {
   /* porovnavame znak po znaku s labelem dokud to jde */	  
   i = 0;
   while (retez[i] != '\0' &&
          label[nalezene].jmeno[i] != '\0' &&
          retez[i] == label[nalezene].jmeno[i]) i++;

   /* pokud se s porovnavanim skoncilo na \0, je to ono */
   if (retez[i] == '\0' &&
       label[nalezene].jmeno[i] == '\0')
    {
     *cislo_labelu = nalezene;
     return OK;
    }
  }

 /* label nebyl rozpoznan - indikujeme, ale neni to apriori chyba */
 *cislo_labelu = LABEL_NENALEZEN;
 return OK;
}


/*
 * pridej_label
 * prida to tabulky labelu jeden label
 * novy label se nekontroluje na existenci
 * (in) hodnota: program counter, na ktery ma byt label nastaven
 * (in) retez: nazev labelu
 * (out) cislo: cislo nove vytvoreneho labelu
 * navrat: OK nebo CHYBA v pripade chybne alokace pameti
 */
int pridej_label(int hodnota, char *retez, int *cislo)
{
	/* dynamicky zvetsujeme rozsah pole label */
	if (pocet_labelu == max_pocet_labelu)
	{
		T_LABEL *pom;

		pom = (T_LABEL*) malloc(2 * max_pocet_labelu *
				        sizeof(T_LABEL));
		if (pom == NULL)
		{
                     vysledek_nacteni = CHYBA;
                     return CHYBA;
		}

		memcpy(pom, label, sizeof(T_LABEL)*max_pocet_labelu);
		max_pocet_labelu *= 2;
		free(label);
		label = pom;
	}

	label[pocet_labelu].hodnota = hodnota;
	strcpy(label[pocet_labelu].jmeno, retez);
	*cislo = pocet_labelu;
	pocet_labelu++;
	return OK;
}


/*
 * pridej_nahradu_labelu
 * do tabulky nahrad_label prida novou polozku
 * (in) pc: ktera instrukce se ma menit
 * (in) parametr: ktery parametr instrukce se ma menit
 * (in) label: na ktery label se instrukce odkazuje
 */
int pridej_nahradu_labelu(int pc, int parametr, int label)
{
	/* dynamicky menime rozsah pole nahrad_label */
	if (pocet_nahrad_labelu == max_nahrad_labelu)
	{
		T_NAHRAD_LABEL *pom;

		pom = (T_NAHRAD_LABEL*) malloc(2 * max_nahrad_labelu *
				        sizeof(T_NAHRAD_LABEL));
		if (pom == NULL)
		{
                     vysledek_nacteni = CHYBA;
                     return CHYBA;
		}

		memcpy(pom, nahrad_label, 
		       sizeof(T_NAHRAD_LABEL)*max_nahrad_labelu);
		max_nahrad_labelu *= 2;
		free(nahrad_label);
		nahrad_label = pom;
	}

	nahrad_label[pocet_nahrad_labelu].adresa = pc;
	nahrad_label[pocet_nahrad_labelu].parametr = parametr;
	nahrad_label[pocet_nahrad_labelu].label = label;
	pocet_nahrad_labelu++;
	return OK;
}


/*
 * nahrad_labely
 * v pameti kodu projede vsechny instrukce s navestimi
 * a doplni spravne hodnoty
 * (inout) pamet_kodu: modifikovany program
 * (in) delka_kodu
 * (out) pc: v pripade chyby adresa spatne instrukce
 * (out) chybny_label: v pripade chyby cislo labelu
 */
int nahrad_labely(INSTRUKCE* pamet_kodu, int delka_kodu, 
		  int *pc, int *chybny_label)
{
	int i;

	for (i=0; i<pocet_nahrad_labelu; i++)
	{
		if (nahrad_label[i].label == LABEL_NEDEFINOVAN)
		{
			*pc = nahrad_label[i].adresa;
			*chybny_label = nahrad_label[i].label;
			return CHYBA;
		}

		pamet_kodu[nahrad_label[i].adresa]
			  [nahrad_label[i].parametr] =
			  label[nahrad_label[i].label].hodnota;
	}
	return OK;
}


/*
 * pridej_debug
 * do tabulky debug_prikazy vlozi novou polozku
 * (in) prikaz: prikaz vkladany do tabulky
 * navrat: OK nebo CHYBA v pripade spatne alokace pameti
 */
int pridej_debug(int prikaz)
{
	if (pocet_debug_prikazu == max_debug_prikazu)
	{
		T_DEBUG_PRIKAZ *pom;
		pom = (T_DEBUG_PRIKAZ*) malloc(2*max_debug_prikazu*
				               sizeof(T_DEBUG_PRIKAZ));
		if (pom == NULL) return CHYBA;
		memcpy(pom, debug_prikazy, max_debug_prikazu*
				           sizeof(T_DEBUG_PRIKAZ));
		free(debug_prikazy);
		debug_prikazy = pom;
		max_debug_prikazu *= 2;
	}

	debug_prikazy[pocet_debug_prikazu][0] = prikaz;
	pocet_debug_prikazu++;
	return OK;
}


/*
 * nacti_debuginfo
 * ze vstupniho souboru nacte prikaz pro debugger
 * a upravi tabulky debug_prikazy a instr_debug_prikazy
 * (in) pc: ke ktere instrukci se bude debugprikaz vztahovat
 */
int nacti_debuginfo(int pc)
{
        int cislo;
        char debug_retez[MAX_PISMEN_INSTRUKCE+1];

	if (nacteny_znak != '&')
	{
		vysledek_nacteni = CHYBA;
		return CHYBA;
	}
	dalsi_znak();
	preskoc_mezery();
	(void) nacti_klic_slovo(&cislo, debug_retez,
				debug_klicova_slova, DEBUG_POCET_KLICSLOV,
				MAX_PISMEN_INSTRUKCE);
	if (vysledek_nacteni != OK) return vysledek_nacteni;

        if (instr_debug_prikazy[pc][0] == DEBUG_NIC)
		instr_debug_prikazy[pc][0] = pocet_debug_prikazu;
	instr_debug_prikazy[pc][1] = pocet_debug_prikazu;

	switch (cislo)
	{
          case DEBUG_VYPIS_REGISTRY:
		  pridej_debug(DEBUG_VYPIS_REGISTRY);
		  break;

	  case DEBUG_VYPIS_ZASOBNIK:
		  pridej_debug(DEBUG_VYPIS_ZASOBNIK);
		  break;

          case DEBUG_VYPIS_AKT_ZAZNAM:
		  pridej_debug(DEBUG_VYPIS_AKT_ZAZNAM);
		  break;
          case DEBUG_VYPIS_ZASOBNIK_OD_DO:
		  if (pridej_debug(DEBUG_VYPIS_ZASOBNIK_OD_DO) != OK)
			  return CHYBA;
		  preskoc_mezery();
		  nacti_cislo(&cislo);
		  debug_prikazy[pocet_debug_prikazu-1][1] = cislo;
		  preskoc_mezery();
		  nacti_cislo(&cislo);
		  debug_prikazy[pocet_debug_prikazu-1][2] = cislo;
		  break;

          case DEBUG_VYPIS_ZASOBNIK_N:
		  if (pridej_debug(DEBUG_VYPIS_ZASOBNIK_N) != OK)
			  return CHYBA;
		  preskoc_mezery();
		  nacti_cislo(&cislo);
		  debug_prikazy[pocet_debug_prikazu-1][1] = cislo;
		  break;

		  case DEBUG_ECHO:
		  if (pridej_debug(DEBUG_ECHO) != OK)
			  return CHYBA;
		  preskoc_mezery();
		  if (pocet_debug_echo_prikazu >= STD_DEBUG_ECHO_PRIKAZU)
			  return CHYBA;
		  if (nacti_retez_do_konce_radku(&(debug_echo_prikazy[pocet_debug_echo_prikazu])) != OK)
			  return CHYBA;
		  debug_prikazy[pocet_debug_prikazu-1][1] = pocet_debug_echo_prikazu;
		  pocet_debug_echo_prikazu++;
		  break;

          default: vysledek_nacteni = CHYBA;
		  return CHYBA;
	}

	return OK;
}



/*
 * nacti_label_instrukci
 * nacte do alokovaneho mista instrukci, predpokladame instrukci s labely
 * (in) pc: je-li instrukce oznacena labelem, je mu prirazena adresa pc
 * (out) instrukce: nactena instrukce
 * navrat: OK nebo CHYBA
 *         nastavuje globalni promennou vysledek_nacteni
 */
int nacti_label_instrukci(int pc, INSTRUKCE *instrukce)
{
 int cislo;
 char instrukce_retez[MAX_PISMEN_INSTRUKCE+1];
 char label_retez[MAX_DELKA_LABELU+1];

 /* instrukce vypada jako
  * mezera* 
  * label?/adresa (zalezi na tom, mame-li absolutni adresovani nebo ne)
  * mezera* 
  * klic_slovo - nazev instrukce
  * mezera* ','?  cislo/label mezera* - parametry instrukce, kolikrat chceme
  * enter
  */
 preskoc_mezery();

 if (absolutni_adresovani == 1)
	 if (nacti_cislo(&cislo) != OK) return CHYBA;   /* cislo instrukce budeme ignorovat */

 if (absolutni_adresovani == 0)
 {
	 if (nacteny_znak == '@') /* nacitame label? */
	 {
		 nacti_label(&cislo, label_retez);
			 if (cislo == LABEL_NENALEZEN)
        		 pridej_label(pc, label_retez, &cislo);
			 else if (label[cislo].hodnota != LABEL_NEDEFINOVAN)
				  {
			 vysledek_nacteni = CHYBA;
			 return CHYBA;
				  }
			 else
			 label[cislo].hodnota = pc;
	 }
 }

 preskoc_mezery();
 if (nacti_klic_slovo(&cislo, instrukce_retez, 
	 klicova_slova, POCET_KLIC_SLOV, 
	 MAX_PISMEN_INSTRUKCE) != OK) return CHYBA;
 (*instrukce)[1] = cislo;

 (*instrukce)[0] = 0;

 while(1)
	 {
	 preskoc_mezery();
	 if (nacteny_znak == ',') 
	  {
	   dalsi_znak();
	   preskoc_mezery();
	  }

	 if (nacteny_znak == '\n')
		 break;

	 if (nacteny_znak == '@') 
	 {
		 if ((*instrukce)[0] >= MAX_PARAMETRU_INSTRUKCE)
		 {
			 vysledek_nacteni = CHYBA;
			 break;
		 }

		 nacti_label(&cislo, label_retez);
		 if (cislo == LABEL_NENALEZEN)
		 {
			 pridej_label(LABEL_NEDEFINOVAN, label_retez, &cislo);
			 pridej_nahradu_labelu(pc, (*instrukce)[0]+2, cislo);
		 }
		 else
			 if (label[cislo].hodnota == LABEL_NEDEFINOVAN)
							  pridej_nahradu_labelu(pc, (*instrukce)[0]+2, cislo);
			 else
							  (*instrukce)[(*instrukce)[0]+2] = label[cislo].hodnota;
	 }
	 else
	 {
		 if ((*instrukce)[0] >= MAX_PARAMETRU_INSTRUKCE)
		 {
			 vysledek_nacteni = CHYBA;
			 break;
		 }

		 if (nacti_cislo(&cislo) == CHYBA) 
			 break;
		 (*instrukce)[(*instrukce)[0]+2] = cislo;
	 }

	 (*instrukce)[0]++;
 }

 if (zkontroluj_instrukci(*instrukce) == CHYBA)
	 vysledek_nacteni = CHYBA;

 return vysledek_nacteni;
}
 

/*
 * nacti_kod
 * nacte ze souboru cely kod
 * (in)    file: vstupni soubor
 * (inout) kod:  zacatek pameti programu, ktera musi byt alokovana
 *               do ni se ulozi nacteny kod
 * (out)   delka_kodu: pocet nactenych instrukci
 * navrat: OK nebo CHYBA
 */
int nacti_kod(FILE *file, INSTRUKCE *kod, int *delka_kodu)
{
 int pc = 0;
 int radek = 0;
 int vysledek_nacteni_instrukce;

 _vstupni_soubor = file;

 vysledek_nacteni = OK;
 dalsi_znak();


 while (!feof(file))
 {
	radek++;
	preskoc_mezery();

	/* za znakem # je komentar */
        if (nacteny_znak == '#') 
	{
                preskoc_zbytek_radku();
		continue;
	}

	/* za znakem & je debuginfo */
	if (nacteny_znak == '&')
	{
		nacti_debuginfo(pc);
		preskoc_zbytek_radku();
		continue;
	}

	/* prazdny radek => preskocit enter a jedeme dal */
	if (nacteny_znak == '\n')
	{
		dalsi_radek();
		continue;
	}

	/* jina moznost neni, nacitame instrukci */
    vysledek_nacteni_instrukce = nacti_label_instrukci(pc, kod+pc);

	if (vysledek_nacteni_instrukce != OK)
	{
		fprintf(stderr, "Chyba nacteni u instrukce %d\n", pc);
		return CHYBA;
	}
	else
	{
	        pc++;
		dalsi_radek();
	}
 }
 *delka_kodu = pc;
 return OK;
} 

   
/*
 * vypis_kod
 * vypisuje zadany pocet instrukci na stdout
 * (in) kod: ukazatel na zacatek pameti dat
 * (in) start: od ktere instrukce se ma vypisovat
 * (in) delka_kodu: kolik instrukci se ma vypsat
 */
void vypis_kod(INSTRUKCE *kod, int start, int delka_kodu)
{
	int i, j, zarovnani;
	char format[20];

	/* spocteme, na kolik znaku chceme zarovnavat
	 * cislo instrukce 
	 */
	i = delka_kodu;
	zarovnani = 1;
	while (i > 10)
	{
		i = i/10;
		zarovnani++;
	}

	/* vytvorime format pro printf */
	sprintf(format, "%%%dd  %%s", zarovnani);


	/* zkoukneme, jestli jsme nevybehli z pameti dat */
	delka_kodu += start;
	if (start < 0) start = 0;
	if (delka_kodu > PAMET_KODU) delka_kodu = PAMET_KODU;

	for (i=start; i<delka_kodu; i++)
	{
		/* musime davat pozor na to, zda je instrukce podporovana */
		if (kod[i][1] < POCET_KLIC_SLOV &&
		    kod[i][1] >= 0)
		{
			printf(format, i, klicova_slova[kod[i][1]]);
			for (j=0; j<kod[i][0]; j++) printf(" %d", kod[i][2+j]);
			printf("\n");
		}
		else
			printf("%d  ?????\n", i);
	}

}


/*
 * debug
 * vypisuje debuginfo
 * (in) pc: instrukce, u ktere se ma info vypisovat
 * (in) vrchol
 * (in) baze
 * (in) data: aktualni stav pocitace
 */
void debug(int pc, int vrchol, int baze, int *data)
{
	int i, j, s_od, s_do;

	if (instr_debug_prikazy[pc][0] == DEBUG_NIC) return;
	for (i =  instr_debug_prikazy[pc][0];
	     i <= instr_debug_prikazy[pc][1];
	     i++)
	{
          switch(debug_prikazy[i][0])
          {
		  case DEBUG_VYPIS_REGISTRY: 
			  printf("%sPC: %d  SP: %d  BASE: %d\n",
					  debug_prefix, pc, vrchol, baze);
			  break;

		  case DEBUG_VYPIS_ZASOBNIK:
			  printf("%sZasobnik:\n", debug_prefix);
			  for (j=1; j<=vrchol; j++)
				  printf("%s%03d %d\t\t\t%x\n", debug_prefix,
						  j, data[j], data[j]);
			  break;
		  case DEBUG_VYPIS_AKT_ZAZNAM:
			  printf("%sZasobnik (akt. zaznam):\n", debug_prefix);
			  for (j=baze; j<=vrchol; j++)
				  printf("%s%03d %d\t\t\t%x\n", debug_prefix,
						  j, data[j], data[j]);
			  break;
		  case DEBUG_VYPIS_ZASOBNIK_OD_DO:
			  s_od = debug_prikazy[i][1];
			  if (s_od < 0) s_od = 0;
			  s_do = debug_prikazy[i][2];
			  printf("%sZasobnik (od adresy %d do adresy %d):\n", debug_prefix, s_od, s_do);
			  if (s_do > PAMET_DAT) s_do = PAMET_DAT;

			  for (j=s_od; j<=s_do; j++)
				  printf("%s%03d %d\t\t\t%x\n", debug_prefix,
						  j, data[j], data[j]);
			  break;
		  case DEBUG_VYPIS_ZASOBNIK_N:
			  printf("%sZasobnik (poslednich %d polozek):\n", debug_prefix, debug_prikazy[i][1]);
			  s_od = vrchol - debug_prikazy[i][1] + 1;
			  if (s_od < 0) s_od = 0;
			  s_do = vrchol;
			  if (s_do > PAMET_DAT) s_do = PAMET_DAT;

			  for (j=s_od; j<=s_do; j++)
				  printf("%s%03d %d\t\t\t%x\n", debug_prefix,
						  j, data[j], data[j]);
			  break;
		  case DEBUG_ECHO:
			  printf("%s%s\n", debug_prefix, debug_echo_prikazy[debug_prikazy[i][1]]);
			  break;
	  }
	}
}


/*
 * definice interpretu PL/0
 */
#include "instrukce_pl0_ext.c"
