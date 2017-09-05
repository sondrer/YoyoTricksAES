/* rijndael-alg-ref.c   v2.2   March 2002
 * Reference ANSI C code
 * authors: Paulo Barreto
 *          Vincent Rijmen
 *
 * This code is placed in the public domain.
 */


/*
Fast Key-Independent Distinguisherfor 5 rounds of AES using around 2^25 texts 
author: Sondre R{\o}njom
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
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

int rijndaelKeySched (word8 k[4][MAXKC], int keyBits, int blockBits, 	word8 W[MAXROUNDS+1][4][MAXBC]) {
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
/*
The layer in front of SLS. Used for verifying that right pair was indeed found.
*/
int Q(word8 a[4][MAXBC],word8 rk[MAXROUNDS+1][4][MAXBC]){
  int BC = 4;
  AddRoundKey(a,rk[0],BC);

  //ShiftRows(a,0,BC);

  Substitution(a,S,BC);
  MixColumns(a,BC);
  AddRoundKey(a,rk[1],BC);
  ShiftRows(a,0,BC);
  return 0;
}

/* Everything above here is code related to AES made by Barreto and Rijmen */

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


void Encrypt (word8 a[4][MAXBC],word8 rk[MAXROUNDS+1][4][MAXBC], int rounds)
/* Encrypt only a certain number of rounds.
 * Only used in the Intermediate Value Known Answer Test.
 */
{
  int r, BC;
  BC = 4;
  AddRoundKey(a,rk[0],BC);
 
  for(r = 0; r < rounds; r++) {
    Substitution(a,S,BC);
    ShiftRows(a,0,BC);
    MixColumns(a,BC);
    AddRoundKey(a,rk[r+1],BC);
  }

}   


int Decrypt (word8 a[4][MAXBC], word8 rk[MAXROUNDS+1][4][MAXBC], int rounds)

{
  int r, BC;
  BC = 4;


  for(r = 0; r < rounds; r++) {
    AddRoundKey(a,rk[rounds-r],BC);
    InvMixColumns(a,BC);  
    ShiftRows(a,1,BC);
    Substitution(a,Si,BC);   
  }
 
  AddRoundKey(a,rk[0],BC);
  
  return 0;
}

/*
Equal to 5 rounds AES encryption minus initial SR and trailing MC,SR
*/
int SuperEnc5(word8 a[4][MAXBC],word8 rk[MAXROUNDS+1][4][MAXBC]){

  int BC = 4;
  AddRoundKey(a,rk[0],BC);

  //ShiftRows(a,0,BC);

  Substitution(a,S,BC);
  MixColumns(a,BC);
  AddRoundKey(a,rk[1],BC);
  ShiftRows(a,0,BC);

  Substitution(a,S,BC);
  MixColumns(a,BC);
  AddRoundKey(a,rk[2],BC);
  Substitution(a,S,BC);

  ShiftRows(a,0,BC);
  MixColumns(a,BC);
  AddRoundKey(a,rk[3],BC);
  ShiftRows(a,0,BC);

  Substitution(a,S,BC);
  MixColumns(a,BC);
  AddRoundKey(a,rk[4],BC);
  Substitution(a,S,BC);

/*
  ShiftRows(a,0,BC);
  MixColumns(a,BC);
  */
  AddRoundKey(a,rk[5],BC);

  return 0;
}

/*
Equal to 5 rounds AES decryption minus initial MCinv,SRinv and trailing SRinv
*/

int SuperDec5(word8 a[4][MAXBC],word8 rk[MAXROUNDS+1][4][MAXBC]){

  int BC = 4;
 
  AddRoundKey(a,rk[5],BC);
  /*
  InvMixColumns(a,BC);
  ShiftRows(a,1,BC);
  */

  Substitution(a,Si,BC);  
  AddRoundKey(a,rk[4],BC);
  InvMixColumns(a,BC);  
  Substitution(a,Si,BC);  
 
  ShiftRows(a,1,BC);
  AddRoundKey(a,rk[3],BC);
  InvMixColumns(a,BC);  
  ShiftRows(a,1,BC);

  Substitution(a,Si,BC);  
  AddRoundKey(a,rk[2],BC);
  InvMixColumns(a,BC);  
  Substitution(a,Si,BC);

  ShiftRows(a,1,BC);
  AddRoundKey(a,rk[1],BC);
  InvMixColumns(a,BC);  
  Substitution(a,Si,BC);

  // ShiftRows(a,1,BC);
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

    // z = randomInRange(0,4);
    for(int i=0; i < 4  ;i++){
      x[i][z] = b[i][z];
      y[i][z] = a[i][z]; 
    }


}

int BadZeroWeightDetected(word8 a[4][MAXBC], word8 b[4][MAXBC]){
  int wt = 0;
  for(int i=0; i< 4; i++){
    wt = 0;
    for(int j=0; j<4; j++){
      if (a[j][i] == b[j][i])
        wt +=1; 
    }
  if (wt >= 2 && wt < 4)
    
      return 1;
  }
  
  return 0;
}


/*
  Repeats the experiment 10 times for a random key and collect data complexity 
  with a proof that right pair was found
*/
int main() {


  int BC = 4;
  sranddev();
  // Init a random AES key
  word8 k[4][MAXKC];
  for(int i=0; i< 4; i++){
    for(int j=0; j < 4; j++){
      k[i][j] = randomByte();
    }
  }
  word8 rk[MAXROUNDS+1][4][MAXBC];
  rijndaelKeySched(k, 128, 128, rk);
  word8 p1[4][MAXBC];
  word8 p2[4][MAXBC];

  // Init variables
  int cnt1=0;
  int cnt2=0;
  int WrongPair=0;
  word8 p1_tmp[4][4];
  word8 p2_tmp[4][4];

  int detected = 0;

  /* 
  Do 10 experiments. Each experiment returns a right pair
  */
  for(int z = 0; z < 10; z++){
    printf("Test %i\n",z);
    printf("\n");
    cnt1 = 0;
    detected = 0;
    int Datacnt = 0; // Counts total data complexity in each experiment

    // continue the experiments until detection of bad pair
    while(detected == 0){ 
     
      cnt1+=1;
     /*
      Generate random plaintext pairs p1,p2. Non-zero difference only in first word.
     */
     for(int i=0; i< 4; i++){
        for(int j=0; j < 4; j++){
          p1[i][j] = randomByte();
        }
      }
      memcpy(p2,p1,sizeof(p2)*sizeof(word8));
     
      for(int i=0; i <4; i++){
        p2[i][0] = randomByte();
      }
   
    cnt2 = 0;
    WrongPair = 0;
    memcpy(p1_tmp,p1,sizeof(p1_tmp)*sizeof(word8));
    memcpy(p2_tmp,p2,sizeof(p2_tmp)*sizeof(word8));
    
    /*
      Generate pairs until bad pair is detected. Right pair continues to the margin.
      We set a general margin at 2^16. Test will end before this if it is a wrong pair. 
      Total data complexity is printed in the end
    */
    while (cnt2 < 65536 && WrongPair == 0 ){
      cnt2 +=1;
      Datacnt+=2;

      SuperEnc5(p1,rk);
      SuperEnc5(p2,rk);

      swap(p1,p2);
     
      SuperDec5(p1,rk);
      SuperDec5(p2,rk);

     // Test for bad pair
      if (BadZeroWeightDetected(p1,p2) == 1)
       WrongPair = 1;
      
      swap(p1,p2);
    }
    // That went well
    if (WrongPair == 0){
      detected = 1;
      printf("Success!");
      printf("satisfying pair was:\n");
      Print(p1_tmp);
      Print(p2_tmp);
      printf("Verification that Zero Difference after Q layer has weight 2:\n");
      Q(p1_tmp,rk);
      Q(p2_tmp,rk);
      PrintXOR(p1_tmp,p2_tmp);
      printf("Found after %i pairs\n",cnt1);
      printf("Amount of plaintexts and ciphertexts: %i (2^%f) \n", Datacnt, log2(Datacnt));
      printf("\n\n");
      
    }
  }
    
  }

}


