#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>


/*
 * RSA avec réduction par division euclidienne
 * Opérations en mode octet.
 * Un mot est un octet uint8_t, un mot double est un uint16_t
 */

// multiplication courte avec deux accumulations a x b + c + carry
// le résultat intermédiaire est un mot double
// rend le poids faible et affecte le poids fort à *carry
// NB. a,b,c,carry <= 2^n - 1 donc
// a x b + c + carry < 2^2n -2.2^n + 1 + 2^n - 1 + 2^n - 1 = 2^2n - 1
// il n'y a donc pas de débordement sur des mots doubles
//////////////////////////////////////////////////////////////////
uint8_t SMul_a_a(uint8_t a, uint8_t b, uint8_t c, uint8_t*carry)
{
	uint16_t p;
	p=(uint16_t)a*(uint16_t)b+(uint16_t)*carry+(uint16_t)c;
	*carry=p>>8;
	return p;
}

// division courte de (carry, x) par y
// algorithme binaire
// le diviseur y doit être supérieur à carry
// rend le quotient et affecte le reste à *carry
//--------------------
static uint8_t SDiv(uint8_t x,uint8_t y,uint8_t*carry)
{
	int i;    // index de boucle
	int8_t c;  // retenue
	uint8_t r;   // reste local

	r=*carry;   // (r,x)
	for (i=8;i>0;--i)
	{   // (c7,r,x) <-- (r,x) * 2 (décalage)
		c= r & 0x80; // retenue = 1er chiffre de (r,x)
		r=(r<<1)+(x>>(8-1));
		x<<=1;
		if ( (c!=0) || (r>=y) )
		{   // test (c7,r,x) >= (y,0)
			++x;  // le chiffre du quotient est inséré à droite de x
			r-=y;
		}
	}
	*carry=r;
	return x;
}

/////////////////////////////////////////////////////////
// procédures multi-précision
// Un entier long est défini par
// - une taille sx = nombre de chiffres en base B
// - une table  x de chiffres en convention little endian
//   le poids suit les adresses croissantes
// Les procédures supposent que le chiffre significatif de poid
// fort est non nul, c'est-à-d x[sx-1]!=
// zéro est le seul entier de taille nulle
/////////////////////////////////////////////////////////

// copie "o" dans "d"
// ne gère pas le recouvrement des origines et destination
////////////////////////////////////////
void LCopy(uint8_t*d,uint8_t so,uint8_t*o)
{
	while (so--)
	{
		*d++=*o++;
	}
}

// multiplication de deux longs
// affecte a "r" le produit de "a" de taille "sa" et de "b" de taille "sb"
// rend la taille du resultat
///////////////////////////////////////////////////////////////////////////
uint8_t LLMul(uint8_t*r,uint8_t sa, uint8_t*a,uint8_t sb, uint8_t*b)
{
	uint8_t i;
	uint8_t j;
	uint8_t carry;
	uint8_t x;
	if ( (sa==0) || (sb==0) )
	{ // si l'un des operandes est nul, le resultat l'est aussi
		return 0;
	}
	carry=0;
	// multiplication par le premier chiffre de b
	// le résultat a*b[0] est affecté au résultat
	for (i=0;i<sa;i++)
	{
		r[i]=SMul_a_a(a[i],b[0],0,&carry);
	}
	r[sa]=carry;
	// les produits par les autres chiffres de b, a*b[j]
	// sont ajoutés au résultat
	for (j=1;j<sb;++j)
	{
		r++;  // écriture décalée dans le résultat
		carry=0;
		x=b[j]; // le chiffre de b par lequel il faut multiplier a
		for (i=0;i<sa;++i)
		{
			r[i]=SMul_a_a(a[i],x,r[i],&carry);
		}
		r[sa]=carry;
	}    
	// calcul de la taille du résultat selon la dernière retenue
	if (carry) return sa+sb;
	else return sa+sb-1;
}


// rend le numero du premier 1 de x a partir de la gauch
// si x= 00100000 --> rend 
//       76543210
static int first_one(int x)
{
	int count;
	count=7;
	while (x<0x80) { --count; x<<=1; }
	return count;
}


// décalage à gauche long de "n" rangs, "n" étant inférieur à 8
static void LShl(int sx, uint8_t*x, int n)
{
	int i;
	for (i=sx-1;i!=0;--i)
	{
		x[i] = (x[i]<<n) + ( x[i-1]>>(8-n) ) ;
	}
	x[0]<<=n;
}

// décalage à droite long de "n" rangs, "n" étant inférieur à 8
static void LShr(int sx, uint8_t*x, int n)
{
	int i;
	for(i=1;i<sx;i++)
	{
		x[i-1]=(x[i-1]>>n) + ( x[i]<<(8-n) );
	}
	x[i-1]>>=n;
}


// division euclidienne d'un entier long par un entier long
// divise "a" (taille "*psa") par "b" (taille "sb")
// le reste est ecrit dans *psa (taille) et a  (chiffres)
// le quotient est ignoré
// "b" doit avoir au moins deux chiffres (taille "sb" >=2, donc non nul !)
// et "a" doit etre superieur a "b";
//
void Modulo(uint8_t*psa,uint8_t*a,int sb,uint8_t*b)
{
    int        count;   // decalage de normalisation
    int        i,k;
    int        sa;
    uint8_t    qp;
    uint8_t    qc[2];
    uint8_t    rc[2];
    uint8_t    t;
    int        sq;
    uint8_t    ah;      // poids fort de a
    uint8_t    rem;
    uint8_t    carry;

    sa=*psa;
    if (sa<sb) return;

    // determiner le decalage de normalisation
    count=8-1-first_one(b[sb-1]);
    if (count>0)
    {
        // normaliser le diviseur, c'est-à-dire faire en sorte que
        // le bit de poids fort du premier chiffre de b soit 1
        LShl(sb,b,count);
        // normaliser le dividende
        ah=a[sa-1]>>(8-count);
        LShl(sa,a,count);
    }
    else ah=0;
    ++sa;
    // gain d'une iteration
    if ( (ah==0) && (a[sa-2]<b[sb-1]) && (sa>3) )
    {
        ah=a[--sa-1];
    }
    sq=sa-sb; // taille du quotient
    for (k=sq;k;--k) // boucle principale
    {
        // estimation du quotient partiel
        if (ah==b[sb-1])
        {
            qp=0xff;
            rem=ah+a[sa-2];
            if (rem<ah) goto soustraire;
        }
        else
        {
            rem=ah;
            qp=SDiv(a[sa-2],b[sb-1],&rem);
        }
        // correction
        rc[0]=a[sa-3];
        rc[1]=rem;
        carry=0;
        qc[0]=SMul_a_a(b[sb-2],qp,0,&carry);
        qc[1]=carry;
        while ( (qc[1] > rc[1]) || ( (qc[1] == rc[1]) && (qc[0] > rc[0]) ) )
        {
            --qp;
            if ( qc[0]<b[sb-2] ) --qc[1];
            qc[0]-=b[sb-2];
            rc[1]+=b[sb-1];
            if (rc[1]<b[sb-1]) break; // debordement ?
        }
        // soustraction
        if (qp)
        {
        soustraire:
            carry=0;
            for (i=0;i<sb;i++)
            {
                t=SMul_a_a(qp,b[i],0,&carry);
                if (t>a[k+i-1]) ++carry;
                a[k+i-1]-=t;
            }
            // derniere correction si nécessaire
            if (carry>ah)
            {
                qp--;
                carry=0;
                for (i=0;i<sb;i++)
                {
                    t=a[k+i-1]+carry;
                    if (t>=carry) carry=0; // sinon, elle reste à 1
                    t+=b[i];
                    if (t<b[i]) carry=1; // ++carry;
                    a[k+i-1]=t;
                }
            }
        }
        sa--;
        ah=a[sa-1];
    }
    while ( (sa>0) && (a[sa-1]==0) ) sa--;
    // denormalisation
    if (count>0)
    {   // du reste
        LShr(sa,a,count);
        // du dividende pour qu'il soit égal à ce qu'il était
        // lors de l'appel
        LShr(sb,b,count);
    }
    // affectation taille du reste
    *psa=sa;
    if (sa!=0)
    {
        if (a[sa-1]==0) --*psa;
    }
}

// variables globales
////////////////////

// Taille maxi du modulo en nombre d'octets
#define MAX 32

// le modulo n
uint8_t sn;
uint8_t n[MAX];



// Multiplication modulo n = multiplication suivi d'une division Euclidienne
// a = a*b mod n
// Le modulo est la variable globale (sn,n)
uint8_t LLMulMod(uint8_t sa, uint8_t*a, uint8_t sb, uint8_t*b)
{
    uint8_t sp;
    uint8_t p[2*MAX]; // là où est calculé le produit
    sp=LLMul(p,sa,a,sb,b);
    Modulo(&sp,p,sn,n);
    LCopy(a,sp,p);
    return sp;
}

// Elévation de x à la puissance e, modulo n (variable globale) résultat dans r
// rend la taille du résultat.
uint8_t LLExpMod(uint8_t*r, uint8_t sx, uint8_t*x, uint8_t se, uint8_t*e)
{
    uint8_t sr;         // taille du résultat
    uint8_t flag;       // initialisé à 0 et mis à 1 quand le résultat est différent de 1
    uint8_t t; // chiffre courant de l'exposant
    uint8_t msk; // masque du bit de l'exposant
    // algorithme avec règle de Horner
    flag=0;
    sr=1;
    r[0]=1; // initialisation par défaut r <-- 1
    while(se!=0)
    { // boucle sur les bits de n du poids fort vers le poids vaible
        t=e[--se];
        for (msk=0x80;msk!=0;msk>>=1)
        {
            if (flag!=0)
            {
                sr=LLMulMod(sr,r,sr,r);
            }
            if ((t&msk)!=0)
            {
                sr=LLMulMod(sr,r,sx,x);
                flag=1;                       // maintenant, il faut élever au carré
            }
        }
    }
    return sr;
}



//
// fonction de lecture et d'affichage en hexadécimal
// nécessaire uniquement pour le mode console
//////////////////////////////////////////////////////

// convertit un caractère ascii en uint8_t
// si le caractère ascii ne correspond pas à un chiffre, rend le mot tout à 1
uint8_t digit(char c)
{
	if ( (c>='0') && (c<='9') ) return c-'0';
	if ( (c>='a') && (c<='z') ) return c-'a'+10;
	if ( (c>='A') && (c<='Z') ) return c-'A'+10;
	return (uint8_t)-1;
}

// décalage de 4 symboles binaires vers la gauche
/////////////////////////////////////////////////
int LShl4(int sx, uint8_t*x)
{
    int i;
    uint8_t c;
    uint8_t t;
    c=0;
    for (i=0;i<sx;i++)
    {
        t=x[i];
        x[i]=(x[i]<<4)+c;
        c=t>>4;
    }
    if (c!=0)
    {
        x[i++]=c;
    }
    return i;
}

// fonctions de conversion chaine hexa --> nombre
// rend le nombre de digits
int AToL(uint8_t*r,char*s)
{
    uint8_t d;
    int sr;
    sr=0;
    d=digit(*(s++));
    if (d<16) r[0]=0;
    while (d<16)
    {
        sr=LShl4(sr,r);
        r[0]+=d; // ajouter le chiffre courant
        if (sr==0)
        {   // ajuster la taille
            if (d!=0) sr++;
        }
        d=digit(*(s++)); // pour le tour suivant
    }
    return sr;
}

// affichage d'un entier en hexadécimal
///////////////////////////////////////
void affiche_hexa(int sx,uint8_t*x)
{
	while (--sx>=0)
	{
		// affichage du chiffre de poids fort au chiffre de poids faible
		printf("%02x",x[sx]);
	}
	printf("\n");
} 

int test_rsa(char*hn, char*hd, char*he, char*m)
{
    // Exposant privé
    uint8_t sd;
    uint8_t d[MAX];
    // Exposant public
    uint8_t se;
    uint8_t e[4];

    // Message clair
    uint8_t sx; uint8_t x[MAX];

    // Cryptogramme
    uint8_t sy; uint8_t y[MAX+1];

    // Message déchiffré
    uint8_t st; uint8_t t[MAX];

    sn=AToL(n,hn);
    sd=AToL(d,hd);
    se=AToL(e,he);
    sx=strlen(m);
    strcpy((char*)x,m);

    st=LLExpMod(t,sx,x,se,e);


    printf("cryptogramme = ");
    affiche_hexa(st,t);

    // déchiffrement
    sy=LLExpMod(y,st,t,sd,d);
    y[sy]=0;

    printf("message = %s\n",y); 
    return strcmp(m,(char*)y);


}

int main()
{
    printf("Hello RSA!\n");
    int r;

    r=test_rsa( "70a72c857055e465000cf9ca3d5d4a0f",
                "21b115e328c83f80be588a636abb3f21",
                "10001",
                "Hello RSA 128_1!");
    printf("%s\n\n",r==0?"OK":"!!");

    r=test_rsa( "70a72c857055e48268459dcb198b71f1",
                "4b1a1dae4ae3edab5b121efddb07beb",
                "3",
                "Hello RSA 128_2!");
    printf("%s\n\n",r==0?"OK":"!!");


    r=test_rsa( "89285e3254d3c85e712db22cd324994c702a50360d8de3a7",
                "16dc0fb30e234c0fbd879db1ddc4dba8d6659dbc8bf68443",
                "3",
                "Hello RSA 192_1!");
    printf("%s\n\n",r==0?"OK":"!!");
    r=test_rsa( "84a288acefd19ae29412bb4f2fc2cffa666e8fd275aff0d58c2f907418140719",
                "586c5b1df5366741b80c7cdf752c8aa5f51be3f7a9612eb0ea96f2d5da0d77b",
                "3",
                "Hello RSA 256_1!");
    printf("%s\n\n",r==0?"OK":"!!");


    r=test_rsa( "68f4ae1b62792228457af7e8952f63a327cebb7aff6cfe596ee716e5477f7807",
                "5eb311ef411c04985825da55535a3725cf852564f7c42dc23a103aa5b85699",
                "10001",
                "Hello RSA 256_2!");
    printf("%s\n\n",r==0?"OK":"!!");


    r=test_rsa( "13cfc485d4a8394cbcaf6030156499ca7b340b1bbc2fddc6ad9c870210006d3b",
                "2f2eb22ac8bb9b3b56639600edf21910918a886bd8738bb5e8dcf2479d46b31",
                "10001",
                "Hello RSA 256_3!");
    printf("%s\n\n",r==0?"OK":"!!");


    r=test_rsa( "6918c6a6af78ff0731e47076993c8eb353273e9b807df03886dede7dc77c6aaf",
                "13e91db97684f5cbe727e02697e161275709fb381dec5854d8c92a55d56ed01",
                "10001",
                "Hello RSA 256_4!");
    printf("%s\n\n",r==0?"OK":"!!");

    return 0;
}
uint8_t ee_sn EEMEM;
uint8_t ee_n[MAXI] EEMEM;
uint8_t ee_se EEMEM;
uint8_t ee_e[MAXI] EEMEM;
uint8_t ee_sd EEMEM;
uint8_t ee_d[MAXI] EEMEM;

void intro_n(uint32_t* data_n){
	int i;
	for (i=0;i<8;i++){
		eeprom_write_word(&ee_n[i],data_n[i]);
	}
}
void intro_e(uint32_t* data_e){
	int i;
	for (i=0;i<8;i++){
		eeprom_write_word(&ee_e[i],data_e[i]);
	}
}
void intro_d(uint32_t* data_d){
	int i;
	for (i=0;i<8;i++){
		eeprom_write_word(&ee_d[i],data_d[i]);
	}
}
void lire_n(){
	n=eeprom_read_word(&data_n[8]);
}

int main(){
	cla=recbytet0();
	ins=recbytet0();
	p1=recbytet0();
	p2=recbytet0();
	p3=recbytet0();
	data
	sw2=0;
	switch(cla){
		case 86 : {
			switch (ins){
				case 0x00 : 
					int i;
					uint8_t data_n[8];
					for (i=0;i<8;i++){
						data_n[i]=recbytet0();
					}
					intro_n(data_n[]);
				case 0x01 : 
					int i;
					uint8_t data_e[8];
					for (i=0;i<8;i++){
						data_e[i]=recbytet0();
					}
					intro_e(data_e[]);
				case 0x02 : intro_d(d);
					int i;
					uint8_t data_d[8];
					for (i=0;i<8;i++){
						data_d[i]=recbytet0();
					}
					intro_n(data_d[]);
				case 0x03 : lire_n();
				case 0x04 : lire_e();
				case 0x05 : chiffe();
				case 0x06 : dechiffre();
				case 0xc0 : get_response();
			}
		}
	}
}
/*
Quelques clés rsa avec leur factorisation

n = 68f4ae1b62792228457af7e8952f63a327cebb7aff6cfe596ee716e5477f7807
d = 5eb311ef411c04985825da55535a3725cf852564f7c42dc23a103aa5b85699
e = 10001
p = 883b40de3fb593b22859d915ee2c0a59
q = c53a68ca2d12f18d6f5b8f3c00ce895f

p = 78ed527cf3c361475954a21e84c704b1
q = de7cd84842147dc34c975e0acfcf03cd
n = 6918c6a6af78ff0731e47076993c8eb353273e9b807df03886dede7dc77c6aaf
d = 13e91db97684f5cbe727e02697e161275709fb381dec5854d8c92a55d56ed01
e = 10001


p = 9b53a0a3f5fbd86af7f0e3ad8dfd9ddc
q = 20a6fadf53d661168d4dda89ad4319a8
n = 13cfc485d4a8394cbcaf6030156499ca7b340b1bbc2fddc6ad9c870210006d3b
d = 2f2eb22ac8bb9b3b56639600edf21910918a886bd8738bb5e8dcf2479d46b31
e = 10001


*/
