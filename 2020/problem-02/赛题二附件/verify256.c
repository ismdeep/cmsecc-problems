
#include <stdlib.h>
#include <stdio.h>
#include <memory.h>
#include <assert.h>

//#define reducedRound 3

typedef unsigned char UINT8;
typedef unsigned long long UINT64;
typedef UINT64 tKeccakLane;

#define KeccakReferences
#define maxNrRounds 24
#define nrLanes 25
#define index(x, y) (((x)%5)+5*((y)%5))
#define KeccakP1600_stateSizeInBytes    200
#define MIN(a, b) ((a) < (b) ? (a) : (b))

static tKeccakLane KeccakRoundConstants[maxNrRounds];
static unsigned int KeccakRhoOffsets[nrLanes];

void KeccakP1600_InitializeRoundConstants(void);
void KeccakP1600_InitializeRhoOffsets(void);
static int LFSR86540(UINT8 *LFSR);



/*******  initialization functions ************/


void KeccakP1600_Initialize(void *state)
{
    memset(state, 0, 1600/8);
}

void KeccakP1600_StaticInitialize(void)
{
    if (sizeof(tKeccakLane) != 8) {
        printf("tKeccakLane should be 64-bit wide\n");
        
    }
    KeccakP1600_InitializeRoundConstants();
    KeccakP1600_InitializeRhoOffsets();
}


static int LFSR86540(UINT8 *LFSR)
{
    int result = ((*LFSR) & 0x01) != 0;
    if (((*LFSR) & 0x80) != 0)
    /* Primitive polynomial over GF(2): x^8+x^6+x^5+x^4+1 */
        (*LFSR) = ((*LFSR) << 1) ^ 0x71;
    else
        (*LFSR) <<= 1;
    return result;
}

void KeccakP1600_InitializeRoundConstants(void)
{
    UINT8 LFSRstate = 0x01;
    unsigned int i, j, bitPosition;
    
    for(i=0; i<maxNrRounds; i++) {
        KeccakRoundConstants[i] = 0;
        for(j=0; j<7; j++) {
            bitPosition = (1<<j)-1; /* 2^j-1 */
            if (LFSR86540(&LFSRstate))
                KeccakRoundConstants[i] ^= (tKeccakLane)1<<bitPosition;
        }
    }
}

void KeccakP1600_InitializeRhoOffsets(void)
{
    unsigned int x, y, t, newX, newY;
    
    KeccakRhoOffsets[index(0, 0)] = 0;
    x = 1;
    y = 0;
    for(t=0; t<24; t++) {
        KeccakRhoOffsets[index(x, y)] = ((t+1)*(t+2)/2) % 64;
        newX = (0*x+1*y) % 5;
        newY = (2*x+3*y) % 5;
        x = newX;
        y = newY;
    }
}




/******* 5 operation functions ************/


#define ROL64(a, offset) ((offset != 0) ? ((((tKeccakLane)a) << offset) ^ (((tKeccakLane)a) >> (64-offset))) : a)

static void theta(tKeccakLane *A)
{
    unsigned int x, y;
    tKeccakLane C[5], D[5];
    
    for(x=0; x<5; x++) {
        C[x] = 0;
        for(y=0; y<5; y++)
            C[x] ^= A[index(x, y)];
    }
    for(x=0; x<5; x++)
        D[x] = ROL64(C[(x+1)%5], 1) ^ C[(x+4)%5];
    for(x=0; x<5; x++)
        for(y=0; y<5; y++)
            A[index(x, y)] ^= D[x];
}

static void rho(tKeccakLane *A)
{
    unsigned int x, y;
    
    for(x=0; x<5; x++) for(y=0; y<5; y++)
        A[index(x, y)] = ROL64(A[index(x, y)], KeccakRhoOffsets[index(x, y)]);
}

static void pi(tKeccakLane *A)
{
    unsigned int x, y;
    tKeccakLane tempA[25];
    
    for(x=0; x<5; x++) for(y=0; y<5; y++)
        tempA[index(x, y)] = A[index(x, y)];
    for(x=0; x<5; x++) for(y=0; y<5; y++)
        A[index(0*x+1*y, 2*x+3*y)] = tempA[index(x, y)];
}

static void chi(tKeccakLane *A)
{
    unsigned int x, y;
    tKeccakLane C[5];
    
    for(y=0; y<5; y++) {
        for(x=0; x<5; x++)
            C[x] = A[index(x, y)] ^ ((~A[index(x+1, y)]) & A[index(x+2, y)]);
        for(x=0; x<5; x++)
            A[index(x, y)] = C[x];
    }
}

static void iota(tKeccakLane *A, unsigned int indexRound)
{
    A[index(0, 0)] ^= KeccakRoundConstants[indexRound];
}




/*******  permutation functions ************/


void KeccakP1600Round(tKeccakLane *state, unsigned int indexRound)
{

    theta(state);  
    rho(state);
	pi(state);
	chi(state);
	iota(state, indexRound);

}

void KeccakF1600Permute(tKeccakLane *state, unsigned int nRounds){
    for (int n = 0; n < nRounds; n++) {
        KeccakP1600Round(state, n);
    }
}



/****  Compute the hash value of input *****/

void Keccak(int reducedRound, unsigned int rate, unsigned int capacity, const UINT64 *input, 
	unsigned int inputBitLen, UINT64 *output, 
	unsigned int outputBitLen, int level){ 

	if((rate + capacity) != 1600 || (rate % 8) != 0){ 
		printf("rate or capacity is illegal.\n"); 
		return; 
	}
	 

	tKeccakLane state[25]; 
	unsigned int blockSize = 0; 
	unsigned int i; 
	unsigned rateInWords = rate / 64; 


	/* Initialize the state */ 
	KeccakP1600_StaticInitialize(); 
	KeccakP1600_Initialize(state); 
	
	/* Absorb all the input blocks */ 
	int pos = 0; 
	int blocknum = 0; 
	
	while (inputBitLen > pos) { 
		blocknum ++; 
		blockSize = MIN(inputBitLen- pos, rate); 
		//state xor message block
		for (i = 0; i < blockSize; i++) { 
			UINT64 mask = (UINT64)1<< ((pos + i) % 64); 
			state[i/ 64] ^= input[(pos+i) / 64] & mask; 
		} 
		pos += blockSize;
		 
		//no padding
		if(blockSize == rate){ 
			KeccakF1600Permute(state, reducedRound); 
			blockSize = 0; 
		} 
	} 

	/* Do the padding and switch to the squeezing phase */ 
	/* Add the first bit of padding */ 
	state[blockSize /64 ] ^= (UINT64) 1 << (blockSize % 64); 
	
	/* If the first bit of padding is at position rate - 1,
	we need a whole new block for the second bit of padding */ 
	if (blockSize == (rate - 1)) { 
		KeccakF1600Permute(state, reducedRound); 
	} 

	/* Add the second bit of padding */ 
	state[rateInWords - 1] ^= (UINT64) 1 << 63; 

	/* Switch to the squeezing phase */ 
	KeccakF1600Permute(state, reducedRound); 

	/* Squeeze out all the output blocks */ 
	pos = 0; 
	while(outputBitLen - pos > 0) { 
		blockSize = MIN(outputBitLen, rate); 
		for (i = 0; i < blockSize; i++) { 
			UINT64 mask = (UINT64)1<< (i % 64); 
			output[(pos + i)/ 64] ^= (state[i/ 64] & mask) << (pos % 64); 
		} 
		pos += blockSize; 
		if (outputBitLen - pos > 0){ 
			KeccakF1600Permute(state,reducedRound); 
			blockSize = 0; 
		} 
	} 
} 


/*** print the message and hash value to the screen ***/
void printHash(UINT64 message[], int inputLen, UINT64 *hash, int outputLen) { 
	printf("-The message (lenght = %d): \n",inputLen); 
	for (int i = 0; i <= inputLen / 64 ; i++) { 
		printf("%016llX ",message[i]); 
	} 
	printf("\n-The hash (length = %d): \n",outputLen); 
	for (int i = 0; i <= (outputLen-1) / 64 ; i++) { 
		printf("%016llX ",hash[i]); 
	} 
	printf("\n"); 
} 

void score(UINT64 *hash, int outputLen, int reducedRound){
	const int table_delta[5] = {1,2,3,10,20};
	int ln = 0;
	
	for (int i = 0; i <= outputLen / 64 ; i++) { 
		for(int j =0; j < 64; j++){
			if((hash[i] >> j) & (1L)){
				printf("-The length of 0's is %d for %d rounds Keccak256.\n\n", ln, reducedRound);
				if(ln < 64){
					printf("*** length < 64 : Score = 0. ***\n");
				}else{
					printf("*** Score_%d = %d * %d = %d. ***\n", reducedRound, ln, table_delta[reducedRound-1], ln * table_delta[reducedRound-1]);
				}

				return;
			}else{
				ln++;
			}
		}
	}
}


int main(int argc, const char * argv[]){

	// example1
	//UINT64 message_1[7] = {0x01,0x00,0x00,0x00,0x00,0x01,0x00};
	//unsigned int inputBitLen1 = 447;
	//int reducedRound = 1;
	
	// example2
	UINT64 message_1[5] = {0x01,0x8000000000000000,0x00,0x00,0x00};
	unsigned int inputBitLen1 = 319;
	int reducedRound = 1;
	
	unsigned int outputBitLen = 256;
	UINT64 *hash_1 = (UINT64*)calloc(outputBitLen / 64 + 1, sizeof(UINT64)); 
	
	Keccak(reducedRound, 1088, 512, message_1, inputBitLen1, hash_1, outputBitLen, 0); 
	
	printf("M_1:\n");
	printHash(message_1,inputBitLen1, hash_1, outputBitLen);
	
	//compute score
	score(hash_1, outputBitLen, reducedRound);
	
	return 0;
}




