#include <io.h>
#include <inttypes.h>


//------------------------------------------------
// Programme "hello world" pour carte à puce
// 
//------------------------------------------------


// déclaration des fonctions d'entrée/sortie
// écrites en assembleur dans le fichier io.s
extern void sendbytet0(uint8_t b);
extern uint8_t recbytet0(void);

#define LENGTH_PUK 8

enum { VIERGE , VERROUILLE , BLOQUE, DEVEROUILLE } state EEMEM = VIERGE ; 

  
uint8_t puk[8] EEMEM ;
uint8_t pin [4] EMMEM ; 


int compare (uint8_t *a , uint8_t * b , int n){
  int i ;
  for(i =0 ; i< n ; i++){
    if(a[i] != b[i]){
      return 0 ;
    }
  }
  return 1 ;
}



void intro_perso() {
  if (state != VIERGE){ // Vérifie que l'état permet de rentrer un code PUK, sinon il y a une erreur.
    sw1 = 0x6d ;
    break ;
  }
  if(p3!=10){ 
    sw1 = 0x6c ; // taille erronée
    sw2 = 10 ;      // taille attendue 
  }
  sendbytet0(ins);
  uint8_t data2[p3];
  int i ;
  for(i = 0 ; i<p3 ; i++){
    data2[i]=recbytet0();
  }
  for( i = 0 ; i< 8 ; i++) {
    eeprom_write_byte((puk+i),data2[i]);
  }
  for( i = 0 ; i< 4 ; i++) {
    eeprom_write_byte((pin+i),data2[i+8]);
  }
  sw1 = 0x90 ;
}



void change_chv(){
  if (state != DEVERROUILLE ) {
    sw1 = 0x6d ;
    break ;
  }
  if(p3!=8){
    sw1 = 0xc6 ;
    sw2 = 8 ;
  }
  sendbytet0(ins);
  uint8_t pin1[4];
  uint8_t pin2[4];
  uint8_t pin3[4];
  int i ;
  for(i = 0 ; i< 4 ; i++){
    pin1[i]=recbytet0();
  }
  for(i = 0 ; i< 4 ; i++){
    pin2[i]= recbytet0();
  }
  for(i = 0 ; i<4 ; i++){
    pin3[i]=eeprom_read_byte(pin+i);
  }
  if(compare(pin1,pin3,4)){
    for(i=0 ; i< 4 ; i++){
      eeprom_write_byte(pin+i,pin2[i]);
    }
    else {
      sw1 = 0x98 ;
      sw2 = 0x04 ;
      break ;
    }
  }
  sw1 = 0x90 ;
}


void verif_CHV(){
  if (compare(eeprom_read_word(state),VEROUILLE)==0){// On vérifie que l'utilisation vérify CHV soit bien cohérente. state doit être VEROUILLE
    sw1=0x6d;
    break; // Sinon on sort de la fonction avec un status word indiquant une erreur.
  }
  int i; 
  uint8_t dpin[4];// on déclare un tableau temporaire pour stocker en mémoire la suite de uint8_t ce que l'on va recevoir.
  if (p3!=4) sw1= 0x6c; // on vérife que la taille des données soit bien égale à 4, car un code PIN est de taille 4.
  for (i=0;i<p3;i++){
    dpin[i]=recbytet0(); // On effectue une boucle pour remplir le tableau temporaire.
  }
  uint8_t pin [4];// on déclare un second tableau pour y stocker ce que l'on va extraire de l'EEPROM.
  int j;
  for (j=0;j<4;j++){
    pin[j]=eeprom_read_word(pin+j); // boucle de récupération et de stockage. grace à l'accesseur de lecture eeprom_read_word()
  }
  int comp=compare(dpin,pin); // on crée une variable dans laquelle on stocke le resultat de la fonction qui permet de comparer deux tableaux.
  if (comp==1){
    eeprom_write_word(state,DEVEROUILLE); // si la fonction renvoie 1, alors les deux tableau sont les mêmes, le code PIN est le bon, 
    sw1=0x90; // Et dans un tel cas, state devient DEVEROUILLE et le status word indique que tout s'est bien déroulé. 
  }
  else{ // si le code PIN n'est pas le bon alors la variable nbe qui représentes le nombre d'essais est décrémentée.
    eeprom_write_word(nbe,nbe-1);  
    uint8_t essai=eeprom_read_word(&nbe); // et stocke le nombre d'essaie dans la variable essai , car nbe est dans le EEPROM. 
    sw1=0x98; // ici le status word indique seulement que le PIN est mauvais mais ne dit rien quant au nombre d'essais
    if (essai==0){// On teste s'il reste encore des essai, sinon
      sw1=0x98;// le status word indique qu'il y a une erreur
      sw2=0x40; // le status word repond qu'il n y plus d'esssai.
      eeprom_write_word(state,BLOQUE)// l'etat de la carte passe en mode VEROUILLE
	}
    else{
      sw2=0x04; // ici le status word indique que la carte n'est pas encore bloquée.
    }
  }
}

void unlock_CHV(){
  if (compare(eeprom_read_word(state),BLOQUE)==0){
    sw1=0x6d;
    break;
  }
  uint8_t dpuk[8];
  uint8_t dpin[4];
  int i;
  for (i=0;i<8;i++){
    dpuk[i]=recbytet0();
  }
  for (i=0;i<4;i++){
    dpin[i]=recbytet0();
  }
  uint8_t puk [8];
  int j;
  for (j=0;j<8;j++){
    puk[j]=eeprom_read_word(puk+j);
  }
  int comp=compare(puk,dpuk);
  if (comp==1){
    int k;
    for (k=0;k<4;k++){
      eeprom_write_word(pin+k,dpin[k]);
    }
    eeprom_write_word(state,VERROUILLE);
    sw1=0x98;
  }
  else{
    sw1=0x98;
    sw2=0x40;
  }
}




// variables globales en static ram
uint8_t cla, ins, p1, p2, p3;  // header de commande
uint8_t sw1, sw2;              // status word

int taille;         // taille des données introduites -- est initialisé à 0 avant la boucle
#define MAXI 16     // taille maxi des données lues
uint8_t data[MAXI]; // données introduites

// Procédure qui renvoie l'ATR
void atr(uint8_t n, char* hist)
{
    	sendbytet0(0x3b); 	// définition du protocole
    	sendbytet0(n);		// nombre d'octets d'historique
    	while(n--)		// Boucle d'envoi des octets d'historique
    	{
        	sendbytet0(*hist++);
    	}
}


// émission de la version
// t est la taille de la chaîne sv
void version(int t, char* sv)
{
    	int i;
    	// vérification de la taille
    	if (p3!=t)
    	{
        	sw1=0x6c;	// taille incorrecte
        	sw2=t;		// taille attendue
        	return;
    	}
	sendbytet0(ins);	// acquittement
	// émission des données
	for(i=0;i<p3;i++)
    	{
        	sendbytet0(sv[i]);
    	}
    	sw1=0x90;
}

void out_data(){
  if(p3 != taille){
    sw2 = taille ;
    sw1 = 0x6c ;
    return ; 
  }
  sendbytet0(ins);
  int i ;
  for(i = 0 ; i<taille ; i++){
    sendbytet0(data[i]);
  }
  sw1 = 0x90 ;
}

  
    
    
// commande de réception de données
void intro_data()
{
    	int i;
     	// vérification de la taille
    	if (p3>MAXI)
	{
	   	sw1=0x6c;	// P3 incorrect
        	sw2=MAXI;	// sw2 contient l'information de la taille correcte
		return;
    	}
	sendbytet0(ins);	// acquitement

	for(i=0;i<p3;i++)	// boucle d'envoi du message
	{
	    data[i]=recbytet0();
	}
	taille=p3; 		// mémorisation de la taille des données lues
	sw1=0x90;
}



// Programme principal
//--------------------
int main(void)
{
  	// initialisation des ports
  	ACSR=0x80;
  	DDRA=0xff;
  	DDRB=0xff;
  	DDRC=0xff;
  	DDRD=0x00; 
  	PORTA=0xff;
  	PORTB=0xff;
  	PORTC=0xff;
  	PORTD=0xff;

  	// ATR
  	atr(11,"Hello scard");

	taille=0;
	sw2=0;		// pour éviter de le répéter dans toutes les commandes
  	// boucle de traitement des commandes
  	for(;;)
  	{
    		// lecture de l'entête
    		cla=recbytet0();
    		ins=recbytet0();
    		p1=recbytet0();
	    	p2=recbytet0();
    		p3=recbytet0();
	    	sw2=0;
		switch (cla)
		{
	  	case 0x84:
		    	switch(ins)
			{
			case 0:
			  version(4,"1.00");
			  break;
		  	case 1:
			  intro_data();
			  break;
			case 2:
			  out_data();
			  break ; 
            		default:
			  sw1=0x6d; // code erreur ins inconnu
        		}
			break;
      		default:
        		sw1=0x6e; // code erreur classe inconnue
		}
		sendbytet0(sw1); // envoi du status word
		sendbytet0(sw2);
  	}
  	return 0;
}

