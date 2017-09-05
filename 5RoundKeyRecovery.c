/* rijndael-alg-ref.c   v2.2   March 2002
 * Reference ANSI C code
 * authors: Paulo Barreto
 *          Vincent Rijmen
 *
 * This code is placed in the public domain.
 */

/*
Fast Key Recovery for 5 rounds of AES using <= 2^11 texts 
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

  //0xe,0x9,0xd,0xb 
  //0xb,0xe,0x9,0xd
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

/*
The layer in front of SLS. Used for verifying that right pair was indeed found.
*/
int LinearRelation(word8 a[4][4], word8 b[4][4], word8 candidate_key[4][4]){
  int BC = 4;

  AddRoundKey(a,candidate_key,BC);
  AddRoundKey(b,candidate_key,BC);
  Substitution(a,S,BC);
  Substitution(b,S,BC);
  MixColumns(a,BC);
  MixColumns(b,BC);
  if (a[2][0] == b[2][0]){
    return 1;
  }

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
struct Pair {
    word8 p1[4][MAXBC];
    word8 p2[4][MAXBC];
};
/*

*/

word8 Inv(word8 a)
{
    if (a == 0) return 0;       /* as needed in the context of AES */

    word8 x = Logtable[a];   /* x       is in range [0..255] */
    word8 log_inv = 255 - x;  /* log_inv is in range [0..255] */
    return Alogtable[log_inv];
}
int mod(int a, int b)
{
    int r = a % b;
    return r < 0 ? r + b : r;
}

 /*
  We can now generate 5 new pairs that makes key recovery of the 
  remaining keys extremely efficient. 
 */
int recoverFullKey(word8 candidate_key[4][MAXBC], word8 rk[MAXROUNDS+1][4][MAXBC]){
  word8 p1[4][MAXBC];
  word8 p2[4][MAXBC];
  for(int i=0; i< 4; i++){
    for(int j=0; j < 4; j++){
    p1[i][j] = 0 ;
    p2[i][j] = 0;

    }
  }
  p1[0][0] = 1;

  ShiftRows(p1,1,4);
  ShiftRows(p2,1,4);
  InvMixColumns(p1,4);
  InvMixColumns(p2,4);
  Substitution(p1,Si,4);
  Substitution(p2,Si,4);
  AddRoundKey(p1,candidate_key,4);
  AddRoundKey(p2,candidate_key,4);

  struct Pair Pairs[5];
  struct Pair P;
  for(int i=0; i< 5; i++){
    memcpy(P.p1,p1,sizeof(P.p1)*sizeof(word8));
    memcpy(P.p2,p2,sizeof(P.p2)*sizeof(word8));
    Pairs[i] = P;
    SuperEnc5(p1,rk);
    SuperEnc5(p2,rk);
    swap(p1,p2);
    SuperDec5(p1,rk);
    SuperDec5(p2,rk);
    swap(p1,p2);
  }
  word8 b[4];
  
 // b,e,9,d
  // d,b,e,9
  //9,d,b,e

  word8 beta[4];
  beta[0] = 0xb;
  beta[1] = 0xe;
  beta[2] = 0x9;
  beta[3] = 0xd;
  for(int z=1; z < 4; z++){
  
  int k0 = 0;
  int k1 = 0;
  int k2 = 0;
  int k3 = 0;
  int ByteFound = 0;
  int KeyRecovered = 0;

  while(k0 < 256 && KeyRecovered == 0){
    candidate_key[0][z] = k0;

    
    k1 = 0;
    // Find a solution for the second byte
    while (k1 < 256 && ByteFound == 0){
      int con = 0;
    
      for(int i=0; i<  5; i++){
        b[0] = S[Pairs[i].p1[0][z]^k0] ^ S[Pairs[i].p2[0][z]^k0];
        b[1]= S[Pairs[i].p1[1][z]^k1] ^ S[Pairs[i].p2[1][z]^k1];
        if( mul(Inv(beta[mod(-(z-1),4)]),b[0]) == mul(Inv(beta[mod(-(z-1)+1,4)]),b[1])){
          con++;
        }
      }
     
      if (con == 5){
        ByteFound = 1;
        candidate_key[1][z] = k1;
      }
       k1++;
    }

    if(ByteFound == 1){
      ByteFound = 0;
    }
   
   
    // Find a solution for the third byte
    k2=0;
    while (k2 < 256 && ByteFound == 0){
      int con = 0;
      for(int i=0; i<  5; i++){
        b[0] = S[Pairs[i].p1[0][z]^k0] ^ S[Pairs[i].p2[0][z]^k0];
        b[2]= S[Pairs[i].p1[2][z]^k2] ^ S[Pairs[i].p2[2][z]^k2];
        if( mul(Inv(beta[mod(-(z-1),4)]),b[0]) == mul(Inv(beta[mod(-(z-1)+2,4)]),b[2])){
          con++;
        }
      }
     
      if (con == 5){
        ByteFound = 1;
        candidate_key[2][z] = k2;

      }
      k2++;
    }

    if(ByteFound == 1){
      ByteFound = 0; 
    }
 
    // Find a solution for the fourth byte
    k3 = 0;
    while (k3 < 256 && ByteFound == 0){
      int con = 0;
      // candidate_key[3][z] = k2;
      for(int i=0; i<  5; i++){
        b[0] = S[Pairs[i].p1[0][z]^k0] ^ S[Pairs[i].p2[0][z]^k0];
        b[3]= S[Pairs[i].p1[3][z]^k3] ^ S[Pairs[i].p2[3][z]^k3];
        if( mul(Inv(beta[mod(-(z-1),4)]),b[0]) == mul(Inv(beta[mod(-(z-1)+3,4)]),b[3])){
          con++;
        }
      }
     
      if (con == 5){
        ByteFound = 1;
        candidate_key[3][z] = k3;
      }
       k3++;
    }
    if(ByteFound == 1){
      /*
      Found all
      */
      
     

      printf("%i th subkey found:",z);
    
      Print(candidate_key);
      KeyRecovered = 1;
      
      
      }
      k0++;
    }

  }

  
  return 0;
}

/*
  Tests the condition
*/
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
  Repeats an experiment 10 times for a random key and collect the data complexity 
*/

int main() {
  int BC = 4;
  sranddev();


  word8 k[4][MAXKC];
  word8 rk[MAXROUNDS+1][4][MAXBC];

  // Init variables
  word8 p1[4][MAXBC];
  word8 p2[4][MAXBC];
  unsigned int i;
  int KeyFound=0;
  word8 p1_tmp[4][4];
  word8 p2_tmp[4][4];

  struct Pair Pairs[5];
  int Datacnt = 0; // Counts total data complexity in each experiment
  word8 Z = 123; 
  

  /* 
  Do 10 experiments. Each experiment returns right key
  */
  for(int z = 0; z < 10; z++){
    printf("Test %i\n",z);
    printf("\n");
    // Fix a random AES key
    for(int i=0; i< 4; i++){
      for(int j=0; j < 4; j++){
        k[i][j] = randomByte();
     }
    }
    rijndaelKeySched(k, 128, 128, rk);


    word8 candidate_key[4][4];
    for(int i=0; i < 4; i++){
      for(int j=0; j< 4; j++){
        candidate_key[i][j] = 0;
      }
    }
    KeyFound = 0;
    Datacnt = 0;

    
    struct Pair P;
    i = 0;
    // continues this with until key is detected
    while(KeyFound == 0 && i < 256){ 
      
       /*
        Generate initial plaintext pair p1,p2. Non-zero difference only in first word.
       */
       for(int i=0; i< 4; i++){
          for(int j=0; j < 4; j++){
            p1[i][j] = 0;
            p2[i][j] = 0;
          }
        }
        p1[1][0] = (word8) i;
        p2[0][0] = Z;
        p2[1][0] = Z^(word8)i;
        
      /*
        Generate 4 additional pairs in addition to inital pair
      */
      for(int j=0; j < 5; j++){
        Datacnt+=2;
        memcpy(P.p1,p1,sizeof(P.p1)*sizeof(word8));
        memcpy(P.p2,p2,sizeof(P.p2)*sizeof(word8));
       
        Pairs[j] = P;
       
        SuperEnc5(p1,rk);
        SuperEnc5(p2,rk);

        swap(p1,p2);

        SuperDec5(p1,rk);
        SuperDec5(p2,rk);
       
        swap(p1,p2);
      }
      word8 WrongKey = 0;
      word8 diff[4];
      int wt = 0;

      // Guess key candidates 
      for(int k1=0; k1 < 256; k1++){
        candidate_key[1][0] = (word8) k1;
        for(int k2=0; k2 < 256; k2++){
          candidate_key[2][0] = (word8) k2;
          for(int k3=0; k3 < 256; k3++){
            candidate_key[3][0] = (word8) k3;

            // Assume k00 = k01 + i
            candidate_key[0][0] = (word8)(k1)^(word8)(i);
            
            WrongKey = 0;

            // Check if key holds for all 5 pairs
            int j=0; 
            word8 diff[4];
            while(j < 5 && WrongKey == 0){
              for(int r =0; r  < 4; r++){
                diff[r] = (S[Pairs[j].p1[r][0]^candidate_key[r][0]]) ^ (S[Pairs[j].p2[r][0]^candidate_key[r][0]]);
              }
              if ((diff[0]^diff[1]^mul(2,diff[2])^mul(3,diff[3])) != 0){
                WrongKey = 1;
              }
              j++;
            }
         
            // printf("\n");
            if (WrongKey == 0){
              
              // Double check whether it is the right one with 3 additional pairs
              j = 0;
              while(j < 3 && WrongKey == 0){
                Datacnt+=2;
                SuperEnc5(p1,rk);
                SuperEnc5(p2,rk);
                swap(p1,p2);
                SuperDec5(p1,rk);
                SuperDec5(p2,rk);
                for(int r =0; r  < 4; r++)
                  diff[r] = (S[p1[r][0]^candidate_key[r][0]]) ^ (S[p2[r][0]^candidate_key[r][0]]);
                
                if ((diff[0]^diff[1]^mul(2,diff[2])^mul(3,diff[3])) != 0)
                 WrongKey = 1;
                
                swap(p1,p2);
                j++;
              }
              /*
                Right subkey is found, now we recover the rest of it 
              */
              if (WrongKey == 0){
                printf("First subkey found:\n");
                Print(candidate_key);
                // printf("Real key is       :\n");
                // Print(rk[0]);
                printf("Amount of plaintexts and ciphertexts to get here: %i (2^%f)\n", Datacnt, log2(Datacnt));
                printf("Now we recover the rest of the key:\n");
                recoverFullKey(candidate_key,rk);
                printf("\n");
                printf("Recovered Key:  ");
                Print(candidate_key);
                printf("Correct  Key :  ");
                Print(rk[0]);

                printf("\n\n");
                KeyFound = 1;
              }
              
            
            }
             
          }
        }
      }

     i +=1;
    }
    printf("Next test\n\n");
  }

  }


