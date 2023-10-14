/*
 *
 * INTERPRET
 * include do refint_asm, definuje funkcionalitu interpretu ROZSIRENEHO vnitrniho jazyka PL/0
 *
 */

/* funkce pro zjisteni pocatecni adresy na urovni, ktera je o l vyssi 
   nez soucasna uroven, ve ktere je prave vykonan program
*/

typedef double PLOVOUCI;

typedef union {
	PLOVOUCI plovouci_hodnota;
	int    int_slozky[2];
} plovouci_v_zasobniku;

#define NACTI_PLOVOUCI_OP(op)	{ op.plovouci_hodnota = *(PLOVOUCI *)(data+vrchol-1); }
#define ZAPIS_PLOVOUCI_OP(op)   { data[vrchol-1] = op.int_slozky[0]; data[vrchol] = op.int_slozky[1]; }

int zjisti_bazi(int l, int baze, int *data, int *nova_baze) 
{
	int bl;

        bl = baze;
        while (l > 0) 
		{
			if (bl < 1 || bl > PAMET_DAT) return CHYBA;
			bl = data[bl];
            l--;
        }

        if (bl < 1 || bl > PAMET_DAT) return CHYBA;
	*nova_baze = bl;
	return OK;
}


/* interpretace generovanych kodu */
int interpret(INSTRUKCE *kod, int *start)
{
 int vrchol, baze, nova_baze;
 INSTRUKCE i;
 int data[PAMET_DAT+1];              /* pamet dat */    
 char mapa_pameti[PAMET_DAT+1];      /* pro informace o halde; nekontroluje se interference se zasobnikem */
 int pc;
 plovouci_v_zasobniku operand1, operand2;

 {
	 int j;
	 for (j=0; j<PAMET_DAT+1; j++) mapa_pameti[j] = 0;
 }

 pc = *start;

 printf("START PL/0\n");
 vrchol = 0;
 data[0] = data[1] = data[2] = data[3] = 0;
 baze = 1;

 do 
 {
  *start = pc;
  if (pc < 0 || pc > PAMET_KODU) return PC_MIMO_ROZSAH;
  
  if(beh_debug) debug(pc, vrchol, baze, data);
  
  i[0] = kod[pc][0];
  i[1] = kod[pc][1];
  i[2] = kod[pc][2];
  i[3] = kod[pc][3];

  if (beh_trasovani) vypis_kod(kod, pc, 1);

  pc++;

  switch (i[1]) 
  {
	case LIT:	vrchol++;
				if (vrchol < 1) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				data[vrchol] = i[3];
				break;

	case OPR:	switch (i[3])
				{
					case NEG :	if (vrchol < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								data[vrchol] = -data[vrchol];
								break;

					case ADD :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] += data[vrchol + 1];
								break;

					case SUB :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] -= data[vrchol + 1];
								break;

					case MUL :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] *= data[vrchol + 1];
								break;

					case DIV :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								if (data[vrchol + 1] != 0) 
									data[vrchol] /= data[vrchol + 1];
								else 
									return DELENI_NULOU;
								break;

					case MOD :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								if (data[vrchol + 1] != 0) 
									data[vrchol] %= data[vrchol + 1];
								else 
									return DELENI_NULOU;
								break;

					case ODD :	if (vrchol < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								data[vrchol] = data[vrchol] % 2;
								break;

					case EQ  :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] = (data[vrchol] == data[vrchol + 1]);
								break;

					case NE  :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
									data[vrchol] = (data[vrchol] != data[vrchol + 1]);
								break;

					case LT  :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] = (data[vrchol] < data[vrchol + 1]);
								break;

					case GE  :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] = (data[vrchol] >= data[vrchol + 1]);
								break;

					case GT  :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] = (data[vrchol] > data[vrchol + 1]);
								break;

					case LE  :	vrchol--;
								if (vrchol < 1) return PODTECENI;
								if (vrchol+1 > PAMET_DAT) return PRETECENI;
								data[vrchol] = (data[vrchol] <= data[vrchol + 1]);
								break;

             }
            break;

	case LOD:	vrchol++;
				if (vrchol < 1) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				if (zjisti_bazi(i[2], baze, data, &nova_baze) != OK)
					return PODTECENI_BAZE;
				nova_baze += i[3];
				if (nova_baze < 0) return PODTECENI;
				if (nova_baze > PAMET_DAT) return PRETECENI;
					data[vrchol] = data[nova_baze];
				break;

	case STO:	if (zjisti_bazi(i[2], baze, data, &nova_baze) != OK)
					return PODTECENI_BAZE;
				nova_baze += i[3];
				if (nova_baze < 0) return PODTECENI;
				if (nova_baze > PAMET_DAT) return PRETECENI;
				if (vrchol < 1) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				data[nova_baze] = data[vrchol];
	     
				if (beh_sto) printf("%d\n", data[vrchol]);
				vrchol--;
				break;

	case CAL:	if (vrchol+3 > PAMET_DAT) return PRETECENI;
				if (vrchol+1 < 1) return PODTECENI;
				if (zjisti_bazi(i[2], baze, data, &nova_baze) != OK)
					return PODTECENI_BAZE;
				data[vrchol + 1] = nova_baze;
				data[vrchol + 2] = baze;
				data[vrchol + 3] = pc;
				baze = vrchol + 1;
				pc = i[3];
				break;

	case RET:	vrchol = baze - 1;
				if (vrchol+3 > PAMET_DAT) return PRETECENI;
				if (vrchol+2 < 1) return PODTECENI;
				pc = data[vrchol + 3];
				baze = data[vrchol + 2];
				break;

	case INT:	vrchol += i[3];
				break;

	case JMP:	pc = i[3];
				break;

	case JMC:	if (vrchol < 1) return PODTECENI; 
				if (vrchol > PAMET_DAT) return PRETECENI;
				if (data[vrchol] == 0) pc = i[3];
				vrchol--;
				break;

	case REA:	vrchol++;
				if (vrchol > PAMET_DAT) return PRETECENI;
				{
					char vstup[80];
					fgets(vstup, 79, stdin);
				    data[vrchol] = atoi(vstup);
				}
				break;

	case WRI:	if (vrchol < 0) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				putchar(data[vrchol]);
				vrchol--;
				break;

	case OPF:	switch (i[3])
				{
					case NEG :	if (vrchol-1 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand1)
								operand1.plovouci_hodnota = -operand1.plovouci_hodnota;
								ZAPIS_PLOVOUCI_OP(operand1)
								break;

					case ADD :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								operand1.plovouci_hodnota += operand2.plovouci_hodnota;
								ZAPIS_PLOVOUCI_OP(operand1)
								break;

					case SUB :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								operand1.plovouci_hodnota -= operand2.plovouci_hodnota;
								ZAPIS_PLOVOUCI_OP(operand1)
								break;

					case MUL :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								operand1.plovouci_hodnota *= operand2.plovouci_hodnota;
								ZAPIS_PLOVOUCI_OP(operand1)
								break;

					case DIV :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								if (operand2.plovouci_hodnota == 0)
									return DELENI_NULOU;
								else
								{
									vrchol -= 2;
									NACTI_PLOVOUCI_OP(operand1)
									operand1.plovouci_hodnota /= operand2.plovouci_hodnota;
									ZAPIS_PLOVOUCI_OP(operand1)
								}
								break;

					case MOD :	return NEZNAMA_INSTRUKCE;
								break;

					case ODD :	return NEZNAMA_INSTRUKCE;
								break;

					case EQ :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								vrchol--;
								data[vrchol] = (operand1.plovouci_hodnota == operand2.plovouci_hodnota);
								break;

					case NE :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								vrchol--;
								data[vrchol] = (operand1.plovouci_hodnota != operand2.plovouci_hodnota);
								break;

					case LT :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								vrchol--;
								data[vrchol] = (operand1.plovouci_hodnota < operand2.plovouci_hodnota);
								break;

					case GE :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								vrchol--;
								data[vrchol] = (operand1.plovouci_hodnota >= operand2.plovouci_hodnota);
								break;

					case GT :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								vrchol--;
								data[vrchol] = (operand1.plovouci_hodnota > operand2.plovouci_hodnota);
								break;

					case LE :	if (vrchol-3 < 1) return PODTECENI;
								if (vrchol > PAMET_DAT) return PRETECENI;
								NACTI_PLOVOUCI_OP(operand2)
								vrchol -= 2;
								NACTI_PLOVOUCI_OP(operand1)
								vrchol--;
								data[vrchol] = (operand1.plovouci_hodnota <= operand2.plovouci_hodnota);
								break;
				}
				break;

	case RTI :	if (vrchol-1 < 1) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				NACTI_PLOVOUCI_OP(operand1);
				vrchol--;
				data[vrchol] = (int) (operand1.plovouci_hodnota);
				break;

	case ITR :	if (vrchol < 1) return PODTECENI;
				operand1.plovouci_hodnota = (PLOVOUCI) data[vrchol];
				data[vrchol] = operand1.int_slozky[0];
				vrchol++;
				if (vrchol > PAMET_DAT) return PRETECENI;
				data[vrchol] = operand1.int_slozky[1];
				break;

	case NEW :	{
				int j = PAMET_DAT;
				while (mapa_pameti[j] && j > 0) j--;
				if (j == 0)
					return CHYBA_UVOLNENI_PAMETI;
				else
				{
					mapa_pameti[j] = 1;
					vrchol++;
					if (vrchol < 1) return PODTECENI;
					if (vrchol > PAMET_DAT) return PRETECENI;
					data[vrchol] = j;
				}
				}
				break;

	case DEL :  if (vrchol < 1) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				if (mapa_pameti[data[vrchol]] == 0)	return CHYBA_UVOLNENI_PAMETI;
				mapa_pameti[data[vrchol]] = 0;
				vrchol--;
				break;

	case LDA :	if (vrchol < 1) return PODTECENI;
		        if (vrchol > PAMET_DAT) return PRETECENI;
				if (data[vrchol] < 1 || data[vrchol] > PAMET_DAT) return CHYBA_ADRESOVANI;
				data[vrchol] = data[data[vrchol]];
				break;

	case STA :	if (vrchol-1 < 1) return PODTECENI;
		        if (vrchol > PAMET_DAT) return PRETECENI;
				if (data[vrchol] < 1 || data[vrchol] > PAMET_DAT) return CHYBA_ADRESOVANI;
				data[data[vrchol]] = data[vrchol-1];
				vrchol -= 2;
				break;

	case PLD :  if (vrchol-1 < 1) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				if (zjisti_bazi(data[vrchol-1], baze, data, &nova_baze) != OK)
					return PODTECENI_BAZE;
				nova_baze += data[vrchol];
				vrchol--;
				if (nova_baze < 1) return PODTECENI;
				if (nova_baze > PAMET_DAT) return PRETECENI;
					data[vrchol] = data[nova_baze];
				break;

	case PST:	if (vrchol-2 < 1) return PODTECENI;
				if (vrchol > PAMET_DAT) return PRETECENI;
				if (zjisti_bazi(data[vrchol-1], baze, data, &nova_baze) != OK)
					return PODTECENI_BAZE;
				nova_baze += data[vrchol];
				if (nova_baze < 1) return PODTECENI;
				if (nova_baze > PAMET_DAT) return PRETECENI;
				data[nova_baze] = data[vrchol-2];
	     
				if (beh_sto) printf("%d\n", data[nova_baze]);
				vrchol -= 3;
				break;

   default:  return NEZNAMA_INSTRUKCE;

  }
 } while (pc);

 printf(" END PL/0\n");
 return OK;

} 

int zkontroluj_instrukci(INSTRUKCE instrukce)
{
	if (instrukce[0] < MIN_PARAMETRU_INSTRUKCE ||
	    instrukce[0] > MAX_PARAMETRU_INSTRUKCE)
	 return CHYBA;
	
	return OK;
}

