/* rijndael-alg-ref.c   v2.2   March 2002
 * Reference ANSI C code
 * authors: Paulo Barreto
 *          Vincent Rijmen
 *
 * This code is placed in the public domain.
 */


/*
Proof of concept: Distinguisher for 4 rounds of AES using 4 texts
author: Sondre R{\o}njom
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rijndael-alg-ref.h"

#define SC	((BC - 4) >> 1)

#include "boxes-ref.dat"

static word8 shifts[3][4][2] = {
  {{0, 0},
   {1, 3},
   {2, 2},
   {3, 1}},
   
  {{0, 0},
   {1, 5},
   {2, 4},
   {3, 3}},
   
  {{0, 0},
   {1, 7},
   {3, 5},
   {4, 4}}
}; 

word8 mul(word8 a, word8 b) {
   /* multiply two elements of GF(2^m)
    * needed for MixColumn and InvMixColumn
    */
	if (a && b) return Alogtable[(Logtable[a] + Logtable[b])%255];
	else return 0;
}

void AddRoundKey(word8 a[4][MAXBC], word8 rk[4][MAXBC], word8 BC) {
	/* Exor corresponding text input and round key input bytes
	 */
	int i, j;
	
	for(i = 0; i < 4; i++)
   		for(j = 0; j < BC; j++) a[i][j] ^= rk[i][j];
}

void ShiftRows(word8 a[4][MAXBC], word8 d, word8 BC) {
	/* Row 0 remains unchanged
	 * The other three rows are shifted a variable amount
	 */
	word8 tmp[MAXBC];
	int i, j;
	
	for(i = 1; i < 4; i++) {
		for(j = 0; j < BC; j++) 
                	tmp[j] = a[i][(j + shifts[SC][i][d]) % BC];
		for(j = 0; j < BC; j++) a[i][j] = tmp[j];
	}
}

void Substitution(word8 a[4][MAXBC], word8 box[256], word8 BC) {
	/* Replace every byte of the input by the byte at that place
	 * in the nonlinear S-box.
         * This routine implements SubBytes and InvSubBytes
	 */
	int i, j;
	
	for(i = 0; i < 4; i++)
		for(j = 0; j < BC; j++) a[i][j] = box[a[i][j]] ;
}
   
void MixColumns(word8 a[4][MAXBC], word8 BC) {
        /* Mix the four bytes of every column in a linear way
	 */
	word8 b[4][MAXBC];
	int i, j;
		
	for(j = 0; j < BC; j++)
		for(i = 0; i < 4; i++)
			b[i][j] = mul(2,a[i][j])
				^ mul(3,a[(i + 1) % 4][j])
				^ a[(i + 2) % 4][j]
				^ a[(i + 3) % 4][j];
	for(i = 0; i < 4; i++)
		for(j = 0; j < BC; j++) a[i][j] = b[i][j];
}

void InvMixColumns(word8 a[4][MAXBC], word8 BC) {
        /* Mix the four bytes of every column in a linear way
	 * This is the opposite operation of Mixcolumns
	 */
	word8 b[4][MAXBC];
	int i, j;
	
	for(j = 0; j < BC; j++)
	for(i = 0; i < 4; i++)             
		b[i][j] = mul(0xe,a[i][j])
			^ mul(0xb,a[(i + 1) % 4][j])                 
			^ mul(0xd,a[(i + 2) % 4][j])
			^ mul(0x9,a[(i + 3) % 4][j]);                        
	for(i = 0; i < 4; i++)
		for(j = 0; j < BC; j++) a[i][j] = b[i][j];
}

int rijndaelKeySched (word8 k[4][MAXKC], int keyBits, int blockBits, 
		word8 W[MAXROUNDS+1][4][MAXBC]) {
	/* Calculate the necessary round keys
	 * The number of calculations depends on keyBits and blockBits
	 */
	int KC, BC, ROUNDS;
	int i, j, t, rconpointer = 0;
	word8 tk[4][MAXKC];   

	switch (keyBits) {
	case 128: KC = 4; break;
	case 192: KC = 6; break;
	case 256: KC = 8; break;
	default : return (-1);
	}

	switch (blockBits) {
	case 128: BC = 4; break;
	case 192: BC = 6; break;
	case 256: BC = 8; break;
	default : return (-2);
	}

	switch (keyBits >= blockBits ? keyBits : blockBits) {
	case 128: ROUNDS = 10; break;
	case 192: ROUNDS = 12; break;
	case 256: ROUNDS = 14; break;
	default : return (-3); /* this cannot happen */
	}

	
	for(j = 0; j < KC; j++)
		for(i = 0; i < 4; i++)
			tk[i][j] = k[i][j];
	t = 0;
	/* copy values into round key array */
	for(j = 0; (j < KC) && (t < (ROUNDS+1)*BC); j++, t++)
		for(i = 0; i < 4; i++) W[t / BC][i][t % BC] = tk[i][j];
		
	while (t < (ROUNDS+1)*BC) { 
        	/* while not enough round key material calculated */
		/* calculate new values */
		for(i = 0; i < 4; i++)
			tk[i][0] ^= S[tk[(i+1)%4][KC-1]];
		tk[0][0] ^= rcon[rconpointer++];

		if (KC != 8)
			for(j = 1; j < KC; j++)
				for(i = 0; i < 4; i++) tk[i][j] ^= tk[i][j-1];
		else {
			for(j = 1; j < KC/2; j++)
				for(i = 0; i < 4; i++) tk[i][j] ^= tk[i][j-1];
			for(i = 0; i < 4; i++) 
                        	tk[i][KC/2] ^= S[tk[i][KC/2 - 1]];
			for(j = KC/2 + 1; j < KC; j++)
				for(i = 0; i < 4; i++) tk[i][j] ^= tk[i][j-1];
	}
	/* copy values into round key array */
	for(j = 0; (j < KC) && (t < (ROUNDS+1)*BC); j++, t++)
		for(i = 0; i < 4; i++) W[t / BC][i][t % BC] = tk[i][j];
	}		

	return 0;
}
      


int Encrypt (word8 a[4][MAXBC],word8 rk[MAXROUNDS+1][4][MAXBC], int rounds)
/* Encrypt only a certain number of rounds.
 * Only used in the Intermediate Value Known Answer Test.
 */
{
	int r, BC;
	BC = 4;
	AddRoundKey(a,rk[0],BC);

	Substitution(a,S,BC);
  MixColumns(a,BC);
  AddRoundKey(a,rk[1],BC);
  
	for(r = 2; r < rounds; r++) {
		Substitution(a,S,BC);
		ShiftRows(a,0,BC);
		MixColumns(a,BC);
		AddRoundKey(a,rk[r],BC);
    
	}

	Substitution(a,S,BC);
	AddRoundKey(a,rk[rounds],BC);

	return 0;
}   


int Decrypt (word8 a[4][MAXBC],	word8 rk[MAXROUNDS+1][4][MAXBC], int rounds)

{
	int r, BC;
	BC = 4;

  AddRoundKey(a,rk[rounds],BC);
	Substitution(a,Si,BC);
	           
	for(r = 1; r < rounds-1; r++) {
		AddRoundKey(a,rk[rounds-r],BC);
		InvMixColumns(a,BC);    
		ShiftRows(a,1,BC);     
		Substitution(a,Si,BC);
		             
	}
 
  AddRoundKey(a,rk[1],BC);
  InvMixColumns(a,BC);      
  Substitution(a,Si,BC);
  AddRoundKey(a,rk[0],BC);
	
	return 0;
}
/*
  We simplify the swap by swapping the first column that is different 
*/
void swap(word8 x[4][MAXBC], word8 y[4][MAXBC]){

  word8 a[4][4]= {{0x1,0x0,0x0,0x0},
                      {0x0,0x2,0x0,0x0},
                      {0x0,0x0,0x3,0x0},
                      {0x0,0x0,0x0,0x4}};
    word8 b[4][4]= {{0x1,0x0,0x0,0x0},
                      {0x0,0x2,0x0,0x0},
                      {0x0,0x0,0x3,0x0},
                      {0x0,0x0,0x0,0x4}};
    memcpy(&a,x,16*sizeof(word8));
    memcpy(&b,y,16*sizeof(word8));
    int z = -1;
    // Pick the first word where texts are different
    for(int i=0; i< 4; i++){
      for(int j=0; j< 4; j++){
        if (x[j][i] != y[j][i]){
          z = i;
          break;
        }

      }
      if (z != -1){
        break;
      }
    }
    for(int i=0; i < 4  ;i++){
      x[i][z] = b[i][z];
      y[i][z] = a[i][z]; 
    }


}
int randomInRange(int min, int max){

  
    int range = max - min + 1;
    int a, b, c, d;

    a = rand() % range;
    b = rand() % range;
    c = rand() % range;
    d = (a*b) % range;
    d = (d+c) % range;

    return (min + d);

}

word8 randomByte(){
    return (word8) randomInRange(0, 255);
}

void PrintXOR(word8 block1[4][MAXBC], word8 block2[4][MAXBC])
{
  int i, j;


  for(i = 0; i < 4; i++) {
    for(j = 0; j < 4; j++) {
      printf("%02X", block1[j][i]^block2[j][i]);
    } printf(" ");
  }
  printf("\n");
}

void Print(word8 block1[4][MAXBC])
{
  int i, j;

 
  for(i = 0; i < 4; i++) {
    for(j = 0; j < 4; j++) {
      printf("%02X", block1[j][i]);
    } printf(" ");
  }
  printf("\n");
}

/*
  This routine repeats the 4 round distinguisher 10 times for random pairs. 
*/
int main() {
  int BC = 4;
  sranddev();
  word8 k[4][MAXKC] = {{0x00, 0x05, 0x0A, 0x0F},
                       {0x01, 0x06, 0x0B, 0x10},
                       {0x02, 0x07, 0x0C, 0x11},
                       {0x03, 0x08, 0x0D, 0x12}};
  for(int i=0; i< 4; i++){
    for(int j=0; j < 4; j++){
      k[i][j] = randomByte();
    }
  }

  word8 rk[MAXROUNDS+1][4][MAXBC];

  rijndaelKeySched(k, 128, 128, rk);


  word8 p1[4][MAXBC] = {{0x50, 0x5F, 0xB9, 0x03},
                        {0x68, 0x08, 0x7F, 0x8B},
                        {0x12, 0xC8, 0x59, 0x83},
                        {0xA4, 0x89, 0x80, 0x59}};
    printf(" 4 Round distinguisher for AES. \n 10 experiments with random pairs under a random key. \n Encrypt a pair, swap, and return a new plaintext pair \n Zero Difference pattern is the same\n");

  for(int z=0; z < 10; z++){


  for(int i=0; i< 4; i++){
    for(int j=0; j < 4; j++){
      p1[i][j] = randomByte();
    }
  }

  word8 p2[4][MAXBC];
  word8 c1[4][MAXBC];
  word8 c2[4][MAXBC];

  memcpy(p2,p1,sizeof(p2)*sizeof(word8));
  for(int i=0; i <4; i++){
    p2[i][0] = randomByte();
  }
  printf("Random pair # %i\n ", z);
  printf("P1:");
  Print(p1);
  printf("P2:");
  Print(p2);
  printf("Diff:");
  PrintXOR(p1, p2);
  printf("\n");

  //printf("Encrypt");
  Encrypt(p1,rk, 4);
  Encrypt(p2,rk, 4);
  memcpy(c1,p1,sizeof(c1)*sizeof(word8));
  memcpy(c2,p2,sizeof(c2)*sizeof(word8));
  printf("C1:");
  Print(c1);
  printf("C2:");
  Print(c2);
  printf("Diff:");
  PrintXOR(c1,c2);

  printf("\n");
  swap(c1,c2);

  printf("C1':");
  Print(c1);
  printf("C2':");
  Print(c2);
  printf("Diff:");
  PrintXOR(c1,c2);
  printf("\n");

  Decrypt(c1,rk, 4);
  Decrypt(c2,rk, 4);

  printf("p1':");
  Print(c1);
  printf("p2':");
  Print(c2);
  printf("Diff:");
	PrintXOR(c1, c2);
  printf("\n\n\n");
  }
  
  return 0;
}
