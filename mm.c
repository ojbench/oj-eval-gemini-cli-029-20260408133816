/*
 *                     Name: Kangping Yao Andrew id: kyao
 * Generally speaking, I use segregated free list combining with best fit
 * to implement this allocator. When the allocator free a new block, it 
 * inserts the block to the free list with appropriate size class. When the
 * allocator needs to malloc a new block, it searches the appropriate free 
 * list and find the best fitted block. if it doesn't find such one, it will
 * search the free list with larger size class. If it cann't find such free
 * block in all free list, the allocator will extend the heap to satisfy 
 * memory need.  In each free list, I use address offset to point to previous
 * free block and next free block for the reason of reducing minimal block 
 * size requirement to improve utility.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

int mm_checkheap(int verbose);

// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                           printf("Checkheap failed on line %d\n", __LINE__);\
                           exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

#define BEST_FIT  //use best fit
/* single word (4) or double word (8) alignment */
#define HEAD 0 //free list head index
#define END 0 // free list end index
#define WSIZE 4           /* Header/footer size(bytes) */
#define DSIZE 8           /* Double word size(bytes) */ 
#define CHUNKSIZE (1<<9) /* Extend heap by this amount(bytes) */
#define FREE 1    /*Free block*/  
#define ALLOC 0   /*Allocated block*/
#define EPILOGUE 0x01 /* Epilogue index*/
#define MIN_BLOCK_SIZE 16 /*minimal block size in terms of bytes*/
#define OVERHEAD    2       /* overhead of header and footer (words) */
#define MAX_HEAP_SIZE (1<<32) /* maximal heap size*/
#define MAX_BLOCK_SIZE 0xffffffff 
#define BLOCK_SIZE_MARK 0x7ffffffe //1-30 bits are block size area
#define NUM_OF_CLASS 8
#define FREE_BLOCK_SIZE1 4
#define FREE_BLOCK_SIZE2 6
#define FREE_BLOCK_SIZE3 8
#define FREE_BLOCK_SIZE4 32
#define FREE_BLOCK_SIZE5 128
#define FREE_BLOCK_SIZE6 512
#define FREE_BLOCK_SIZE7 1024

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)
#define MAX(x, y) ((x) > (y) ? (x) : (y))

static uint32_t *heap_listp;
static uint32_t *free_list_head_array[NUM_OF_CLASS];
static uint32_t *free_list_head;
#ifdef NEXT_FIT
static uint32_t* rover; /*Next fit rover*/
#endif

static void* place(uint32_t* block, uint32_t asize);
static void* extend_heap(uint32_t word);
static uint32_t *coalesce(uint32_t *bp);
//static int deleteFreeBlock(uint32_t* block);
int checkFreeList(void);
/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void * p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void * p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static inline int in_heap(const void* p) {
	if(p >= mem_heap_hi()){
		dbg_printf("high: %p\n", p);
	}else if(p <= mem_heap_lo()){
		dbg_printf("low: %p\n", p);
	}
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

/* 
 * Return the size of the given block in multiples of the word size
 * including header and footer.
 */
static inline unsigned int block_size(const uint32_t* block) {
    
    
    return (block[0] & BLOCK_SIZE_MARK);
}

// Return true if the block is free, false otherwise
static inline int block_free(const uint32_t* block) {
    
    
    return !(block[0] & 0x01);
}

/* 
 * Mark the given block as input free(1)/allocted(0)
 * by marking the header and footer.
 */
static inline void block_mark(uint32_t* block, int free) {
    
    

    unsigned int footerIndex = block_size(block) - 1;
    block[0] = free ? block[0] & (int) ~0x1: block[0] | 0x1;
    block[footerIndex] = block[0];
}

/* 
 * Mark the MSB in the header of free block which is in free list.
 * Use this to check whether all free block is in list.
 */
static inline void free_block_mark(uint32_t* block) {
    
    

	unsigned int footerIndex = block_size(block) - 1;
    block[0] = block[0] | (1<<31);
	block[footerIndex] = block[0];
}

/* 
 * Sweep the MSB in the header of free block.
 * Use this to check whether all free block is in list.
 */
static inline void free_block_sweep(uint32_t* block) {
    
    
	unsigned int footerIndex = block_size(block) - 1;
    block[0] = block[0] & ~(1<<31);
	block[footerIndex] = block[0];
}

/* 
 * Return true if the free block marked, false otherwise
 */
static inline int free_block_marked(uint32_t* block) {
    
    

    return block[0] & (1<<31);
}

// Return a pointer to the memory malloc should return
static inline uint32_t* block_mem(uint32_t* const block) {
    
    
    

    return block + 1;
}

// Return the header to the previous block
static inline uint32_t* block_prev(uint32_t* const block) {
    
    

    return block - block_size(block - 1);
}

// Return the header to the next block
static inline uint32_t *block_next(uint32_t* const block) {
    
    

    return block + block_size(block);
}

/*
 * Return the address which stores the offset to the
 * previous free block in the free list
 */ 
static inline int* get_prev_ptr(uint32_t* block){
	
	return (int*)(block+1);
}

/*
 * Return the address which stores the offset to the
 * next free block in the free list
 */
static inline int* get_next_ptr(uint32_t* block){
	
	return (int*)(block+2);
}

/* Write a word at address p */
static inline void put(uint32_t* p, uint32_t val) {
	*p = val;
}

/* Read a word at address p */
static inline uint32_t get(uint32_t* p) {
	return *p;
}

/* Set offset in free list*/
static inline void putOffset(int* bp, int val){
	
    
	*bp = val;
}

/* Get offset in free list*/
static inline int getOffset(int* bp){
	
    

	return *bp;
}

/* Compute the address of the block header*/
static inline uint32_t *getHeader(uint32_t* const block){
	
    	
	return block;
}

/* Compute the address of the block footer*/
static inline uint32_t *getFooter(uint32_t* block){
	
    
	block = block + block_size(block) - 1;
	return block;
}

/* Return the class index according to the block size*/
static inline int getClassIndex(uint32_t blockSize){
	if(blockSize <=  FREE_BLOCK_SIZE1){
		return 0;
	}else if(blockSize <= FREE_BLOCK_SIZE2){
		return 1;
	}else if(blockSize <= FREE_BLOCK_SIZE3){
		return 2;
	}else if(blockSize <= FREE_BLOCK_SIZE4){
		return 3;
	}else if(blockSize <= FREE_BLOCK_SIZE5){
		return 4;
	}else if(blockSize <= FREE_BLOCK_SIZE6){
		return 5;
	}else if(blockSize <= FREE_BLOCK_SIZE7){
		return 6;
	}else{
		return 7;
	}
	return -1;
}

/* Return the class index according to the block size */
static inline uint32_t getClassSize(int index){
	if(index == 0){
		return FREE_BLOCK_SIZE1;
	}else if(index == 1){
		return FREE_BLOCK_SIZE2;
	}else if(index == 2){
		return FREE_BLOCK_SIZE3;
	}else if(index == 3){
		return FREE_BLOCK_SIZE4;
	}else if(index == 4){
		return FREE_BLOCK_SIZE5;
	}else if(index == 5){
		return FREE_BLOCK_SIZE6;
	}else if(index == 6){
		return FREE_BLOCK_SIZE7;
	}else if(index == 7){
        return FREE_BLOCK_SIZE7;
	}
	return -1;
}

/*Delete a free block from the list*/
static inline int deleteFreeBlock(uint32_t* block){
	
    
	//get the index of the appropriate free list
	int classIndex = getClassIndex(block_size(block));
	free_list_head = free_list_head_array[classIndex];
	int prevOffset = getOffset(get_prev_ptr(block));
	int nextOffset = getOffset(get_next_ptr(block));
	uint32_t* prev_free_block_ptr = block - prevOffset;
	uint32_t* next_free_block_ptr = block + nextOffset;
	if(prevOffset == HEAD){
		if(nextOffset == END){
			free_list_head = NULL;//no free block
			free_list_head_array[classIndex] = free_list_head;
			return 0;
		}
		//set the next free block as list head
		putOffset(get_prev_ptr(next_free_block_ptr), HEAD);
		free_list_head = next_free_block_ptr;
		free_list_head_array[classIndex] = free_list_head;
		return 0;
	}else{
		if(nextOffset == END){//delete end node
			putOffset(get_next_ptr(prev_free_block_ptr), END);
			return 0;
		}
		//Link the previous and the next free block of current block
		putOffset(get_prev_ptr(next_free_block_ptr), 
					(next_free_block_ptr-prev_free_block_ptr));
		putOffset(get_next_ptr(prev_free_block_ptr),
					(next_free_block_ptr-prev_free_block_ptr));
		return 0;
	}
	return -1;
}

/* Extend heap by the number of word */
static void *extend_heap(uint32_t words){
	uint32_t *bp;
	uint32_t size;
	/*Align the size to the multiple of 8*/
	size = (words % 2) ? (words+1) : words;
	if((long)(bp = mem_sbrk(size*WSIZE))==-1)
		return NULL;	
	bp -= 1; //overwrite original epilogue;
	put(getHeader(bp), size);
	block_mark(bp, FREE);
	put(getHeader(block_next(bp)), EPILOGUE); /*New epilogue header*/
	bp = coalesce(bp);
	int classIndex = getClassIndex(block_size(bp));
	free_list_head = free_list_head_array[classIndex];
	putOffset(get_prev_ptr(bp), HEAD);
	if(free_list_head != NULL){
		putOffset(get_next_ptr(bp), (free_list_head - bp));
		putOffset(get_prev_ptr(free_list_head), (free_list_head - bp));
	}else{
		putOffset(get_next_ptr(bp), END);
	}
	free_list_head_array[classIndex] = getHeader(bp);
	return bp;
}

/*Coalesce free block based on 4 kinds of cases.*/
static uint32_t *coalesce(uint32_t *bp){
	 /*1 free, 0 allocated*/
	size_t prev_alloc = block_free(getFooter(block_prev(bp))); 
	 /*1 free, 0 allocated*/
	size_t next_alloc = block_free(getHeader(block_next(bp))); 
	size_t size = block_size(getHeader(bp));
	/*previous and next block are all allocated */
	if(!(prev_alloc || next_alloc)){ 
		return bp;
	}else if((!prev_alloc) && next_alloc){ /*next block is free*/
		size+=block_size(getHeader(block_next(bp)));
		//delete this free block and add to new list later
		deleteFreeBlock(block_next(bp));
		put(getHeader(bp), size);
		block_mark(bp, FREE);
	}else if( prev_alloc && (!next_alloc)){ /*previous block is free*/
		size += block_size(getHeader(block_prev(bp)));
		bp = block_prev(bp);
		//delete this free block and add to new list later
		deleteFreeBlock(bp);
		put(getHeader(bp), size);
		block_mark(bp, FREE);
	}else{  /*previous block and next block are both free*/
		size += block_size(getHeader(block_prev(bp))) +
			block_size(getFooter(block_next(bp)));
		//delete both free blocks and add them to new list later
		deleteFreeBlock(block_prev(bp));
        deleteFreeBlock(block_next(bp));
		bp = block_prev(bp);
		put(getHeader(bp), size);
		block_mark(bp, FREE);
	}		
	#ifdef NEXT_FIT
		/* Make sure the rover isn't pointing into the free block */
		/* that we just coalesced */
		if((rover > bp) && (rover < block_next(bp)))
			rover = bp;
	#endif
	return bp;
}

/* Find free block with three methods*/
static uint32_t* find_fit(uint32_t words){
	uint32_t blocksize;
	if(words == 0)
		return NULL;	
	int classIndex = getClassIndex(words);
	uint32_t* bptr = free_list_head_array[classIndex];	
#ifdef NEXT_FIT
	int free;
	uint32_t* oldrover = rover;
	/* Search from rover to the end of list */
	while(block_size(rover)>0){
		blocksize = block_size(rover);
		free =  block_free(rover);
		if(free && (blocksize>=words))
			return rover;
		rover = block_next(rover);
	}
	/* Search from start of list to old rover */
	rover = heap_listp;
	while(rover < oldrover){
		blocksize = block_size(rover);
		free =  block_free(rover);
		if(free && (blocksize >= words))
			return rover;
		rover = block_next(rover);
	}
	return NULL;
#endif

#ifdef BEST_FIT
	uint32_t bestSize = MAX_BLOCK_SIZE;
	uint32_t* bestBlock = NULL;
	while(classIndex < NUM_OF_CLASS){
		// No free block
		if(bptr != NULL){
		//Search the first free block which fits the block size
			while((blocksize = block_size(bptr))>0){
				if(blocksize == words){
					return bptr;
				}else if (blocksize > words){
					if(blocksize < bestSize){
						bestSize = blocksize;
						bestBlock = bptr;
					}
				}

				if(getOffset(get_next_ptr(bptr)) == END){
					if(bestBlock != NULL){
						return bestBlock;
					}
					break;
				}
				bptr +=  getOffset(get_next_ptr(bptr));
			}
		}
		classIndex++;
		bptr = free_list_head_array[classIndex];
	}
	return NULL;
#else
	while(classIndex < NUM_OF_CLASS){
		// No free block
		if(bptr != NULL){
		//Search the first free block which fits the block size
			while(block_size(bptr)>0){
				blocksize = block_size(bptr);
				if(blocksize>=words)
					return bptr;
				if(getOffset(get_next_ptr(bptr)) == END){
					break;
				}
				bptr +=  getOffset(get_next_ptr(bptr));
			}
		}
		classIndex++;
		bptr = free_list_head_array[classIndex];
	}
	return NULL;
#endif
}

/*Set the allocated area as allocated and do splitting if necessary*/
static void* place(uint32_t* block, uint32_t asize){
	
    
	uint32_t oldsize;
	int remainder;
	int classIndex;
	uint32_t* nextBlock;
	oldsize = block_size(block);
	remainder = oldsize*WSIZE - asize;	
	
	//delete the original free block from the free list
	deleteFreeBlock(block);
	/*
	 * Allocate whole free block if remainder is less 
	 * than minimal block size(16 bytes).
	 */
	if(remainder < MIN_BLOCK_SIZE){ 
		block[0] = oldsize;
		block_mark(block, ALLOC);
	}else{
		block[0] = asize/WSIZE;
		block_mark(block, ALLOC);
		nextBlock = block_next(block);
		put(getHeader(nextBlock), remainder/WSIZE);
		block_mark(nextBlock, FREE);
		//add splitting free block to the appropriate free list
		classIndex = getClassIndex(remainder/WSIZE);
		free_list_head = free_list_head_array[classIndex];
		putOffset(get_prev_ptr(nextBlock), HEAD);
		if(free_list_head != NULL){
			putOffset(get_next_ptr(nextBlock), (free_list_head - nextBlock));
			putOffset(get_prev_ptr(free_list_head), 
						(free_list_head - nextBlock));
		}else{
			putOffset(get_next_ptr(nextBlock), END);
		}
		free_list_head = nextBlock;
		free_list_head_array[classIndex] = free_list_head;
	}
	return block_mem(block);
} 
/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1;
	put(heap_listp, 0);   /*Alignment padding*/
	put(heap_listp + 1, OVERHEAD); /* Prologue header */
	block_mark(heap_listp + 1,ALLOC); /*Set alloc bit and footer*/
	put(heap_listp + 3, EPILOGUE); /* Epilogue header */
	heap_listp += 3; //point to epilogue 
	// initialize free list array 
	for(int i=0; i<NUM_OF_CLASS; i++)
		free_list_head_array[i] = NULL;
	free_list_head = NULL;
	#ifdef NEXT_FIT
		rover = heap_listp;
	#endif	
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
	checkheap(1);
    return 0;
}

/*
 * search the free list array to get the best fitted 
 * free block. If no such block, then extend the heap
 */
void *malloc (size_t size) {
	checkheap(1);
    uint32_t asize;  /*Adjusted block size*/
	uint32_t extendsize; /*Amount to extend heap if not fit*/
	uint32_t* bp;   
	if(size == 0)
		return NULL;
		
	if((uint32_t)size <= DSIZE)
		asize = 2*DSIZE;
	else
		asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);

	/*Search the free list for a fit*/
	if((bp = find_fit(asize/WSIZE))!=NULL){
		place(bp, asize);
		checkheap(1);
		return block_mem(bp);
	}	
	/*No fit found. Get more memory*/
	extendsize = MAX(asize, CHUNKSIZE);
	if((bp = extend_heap(extendsize/WSIZE)) == NULL){
		return NULL;
	}
	place(bp, asize);
	checkheap(1);
	return block_mem(bp);
}

/*
 * implemented first fit, next fit, best fit.
 * At last, I use best fit with segregated free list.
 */
void free (void *ptr) {
	checkheap(1);
    if (ptr == 0) {
        return;
    }
	//get the block pointer
	uint32_t* bp = (uint32_t*)((char*)ptr-WSIZE);
	block_mark(bp, FREE);
	bp=coalesce(bp);
	//add the new free block to the appropriate free list
	int classIndex = getClassIndex(block_size(bp));
	free_list_head = free_list_head_array[classIndex];
	putOffset(get_prev_ptr(bp), HEAD);
	if(free_list_head != NULL){
		putOffset(get_next_ptr(bp), (free_list_head - bp));
		putOffset(get_prev_ptr(free_list_head), (free_list_head - bp));
	}else{
		putOffset(get_next_ptr(bp), END);
	}
	free_list_head = bp;
	free_list_head_array[classIndex] = free_list_head;
	checkheap(1);
	return;
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block. 
 */
void *realloc(void *oldptr, size_t size) {
	uint32_t oldSize;
	void *newptr;
	uint32_t asize;  /*Adjusted block size*/
	int classIndex;
	checkheap(1);
	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL) {
		return malloc(size);
	}
 	/*Adjust size*/
	if((uint32_t)size <= DSIZE)
		asize = 2*DSIZE;
	else
		asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);
	
	/* Copy the old data. */
	uint32_t* oldHeader = (uint32_t*)((char*)oldptr-WSIZE);
	oldSize = block_size(oldHeader);
	oldSize *= WSIZE; /*words to bytes*/ 
	if((int)(oldSize - asize) < MIN_BLOCK_SIZE && (int)(oldSize - asize) >=0){
		return oldptr;
	}
	/* New size is less than old size, no need to allocate a new area*/
	if(asize < oldSize){
		/* Set the allocated area as allocated and do splitting*/
		put(oldHeader, asize/WSIZE);
		block_mark(oldHeader, ALLOC);
		put(block_next(oldHeader), (oldSize-asize)/WSIZE);
		block_mark(block_next(oldHeader), FREE);
		/* 
 		 * Coalesce the rest memory, in this case the previous block must be
		 * allocated.
		 */
        coalesce(block_next(oldHeader));
		//Update free list head
		classIndex = getClassIndex(block_size(block_next(oldHeader)));
		free_list_head = free_list_head_array[classIndex];
		putOffset(get_prev_ptr(block_next(oldHeader)), HEAD);
		if(free_list_head==NULL){
			 putOffset(get_next_ptr(block_next(oldHeader)), END);
		}else{
			putOffset(get_next_ptr(block_next(oldHeader)), 
					free_list_head-block_next(oldHeader));
			putOffset(get_prev_ptr(free_list_head), 
					(free_list_head - block_next(oldHeader)));
		}
		free_list_head = block_next(oldHeader);
		free_list_head_array[classIndex] = free_list_head;
		checkheap(1);
		return oldptr;
	}
	//The old size is not enough, but next block is free, just extend to it
	else if(block_free(block_next(oldHeader)) && 
			(oldSize+block_size(block_next(oldHeader))*WSIZE)>=asize)
	{
		int restSize = oldSize+block_size(block_next(oldHeader))*WSIZE-asize;
		if(restSize < MIN_BLOCK_SIZE){
			//Delete whole free block
			deleteFreeBlock(block_next(oldHeader));
			put(oldHeader, (asize+restSize)/WSIZE);
			block_mark(oldHeader, ALLOC);
		}else{
			deleteFreeBlock(block_next(oldHeader));
			put(oldHeader, asize/WSIZE);
			block_mark(oldHeader, ALLOC);
			put(block_next(oldHeader), restSize/WSIZE);
			block_mark(block_next(oldHeader), FREE);
			//Insert the new free block to list
			classIndex = getClassIndex(restSize/WSIZE);
			free_list_head = free_list_head_array[classIndex];
			putOffset(get_prev_ptr(block_next(oldHeader)), HEAD);
			if(free_list_head==NULL){
				putOffset(get_next_ptr(block_next(oldHeader)), END);
			}else{
				putOffset(get_next_ptr(block_next(oldHeader)), 
					free_list_head-block_next(oldHeader));
				putOffset(get_prev_ptr(free_list_head), 
					(free_list_head - block_next(oldHeader)));
			}
			free_list_head = block_next(oldHeader);
			free_list_head_array[classIndex] = free_list_head;
		}
		checkheap(1);
		return oldptr;
	}	 
	/* 
 	 * the original block is not enough.
 	 * Allocated a new area and free the original one
 	 */ 
	newptr = malloc(size);
	if(!newptr){
		return 0;
	}
	if((uint32_t)size<oldSize) 
		oldSize = size;
	memcpy(newptr, oldptr, oldSize);
	//free old block
	free(oldptr);
	checkheap(1);
	return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
	size_t bytes = nmemb * size;
	void *newptr;
	checkheap(1);
	newptr = malloc(bytes);
	memset(newptr, 0, bytes);
	checkheap(1);
	return newptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
        verbose = verbose;
        return 0;
}

team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

int checkFreeList(void){
	/*check free list*/
	for(int i=0; i < NUM_OF_CLASS; i++){
		free_list_head = free_list_head_array[i];
		uint32_t* fList = free_list_head;
		int prevOffset;
		int nextOffset;
		if(free_list_head != NULL){
			free_block_mark(free_list_head);
			if((prevOffset = getOffset(get_prev_ptr(free_list_head)))
				!=HEAD){
				printf("Wrong free list head: %d, fList Address: %p\n",
					prevOffset, (void*)free_list_head );
				return 1;
			}
			//If there is a cycle, the loop will not end
			while(getOffset(get_next_ptr(fList))!=END){
				//check whether allocated block is in free list
				if(!block_free(fList)){
					printf("Allocated block is in free list at address: %p" 
						"flist: %p\n", (void*)fList, 
						(void*)free_list_head);
					return 1;
				}
				//mark the free block in the free list
				free_block_mark(fList);
				//check whether free list has block with wrong size
				if(i==0){
					if(block_size(fList) > getClassSize(i)){
						printf("Wrong block size in free list: %d\n",
								i);
						return 1;
					}					
				}else if(i == (NUM_OF_CLASS - 1)){
					if(block_size(fList)<= getClassSize(i)){
						printf("Wrong block size in free list: %d\n",
								i);
						return 1;
					}
				}else{
					if(block_size(fList)<=getClassSize(i-1) &&
					    block_size(fList)>getClassSize(i)){
						printf("Wrong block size in free list: %d\n",
								i);
						return 1;
					}
				}
				nextOffset = getOffset(get_next_ptr(fList));
				fList += nextOffset;//point to next free block
				prevOffset = getOffset(get_prev_ptr(fList)); 
				//check consistency of free list
				if(nextOffset!=prevOffset){
					printf("Free list consecutive error! next: %d, prev: %d,"
							" Address: %p flist: %p\n", nextOffset, 
							prevOffset, (void*)fList, 
							(void*)free_list_head);
					return 1;
				}
			}
			if(!block_free(fList)){//check the end node 
				printf("Allocated block is in free list at address: %p" 
					" flist: %p\n", (void*)fList, (void*)free_list_head);
				return 1;
			}
			free_block_mark(fList);
		}
	}
	return 0;
}
