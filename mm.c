/*
 * mm.c
 * Shastri Ram- shastrir
.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
//static void checkheap(int verbose);
static void checkblock(void *bp);
static void *get_pred(void *bp);
static void *get_succ(void *bp);
static void add_block (void *bp);
static void remove_block (void *bp);

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)

#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)

#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))

#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static long *root = 0 ; //pointer to first free address
#ifdef NEXT_FIT
static long *rover;           /* Next fit rover */
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


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0);                          /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_listp += (2*WSIZE);

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;

#ifdef NEXT_FIT
    rover = root;
#endif

    //mm_checkheap(1);
  return 0;
}


void *malloc (size_t size) {
  //mm_checkheap(1);  // Let's make sure the heap is ok!
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    printf ("malloc %d\n" ,(int)size);
    if (heap_listp == 0){
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= 2*DSIZE)
        asize = 3*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    REQUIRES (bp!=NULL);
    REQUIRES ((size_t)(bp)%8 == 0);

    place(bp, asize);
    return bp;
}



// coalesce - Boundary tag coalescing. Return ptr to coalesced block

static void *coalesce(void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);
  //mm_checkheap(1);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //Case 1 - both allocated
    if (prev_alloc && next_alloc) {
      add_block(bp);
      return bp;
    }

    //Case 3 - prev allocated but next block is free
    else if (prev_alloc && !next_alloc) {
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      PUT(HDRP(bp), PACK(size, 0));
      PUT(FTRP(bp), PACK(size,0));
      remove_block( (void*)( *(long*)( get_succ(bp) ) ) );
      add_block(bp);
    }

    //Case 2 - prev is free but  next is allocated
    else if (!prev_alloc && next_alloc) {
      size += GET_SIZE(HDRP(PREV_BLKP(bp)));
      PUT(FTRP(bp), PACK(size, 0));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      remove_block( (void*)( *(long*)( get_pred(bp) ) ) );
      bp = PREV_BLKP(bp);
      add_block(bp);

    }

    // Case 4 - both prev and next are free
    else {
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
      remove_block( (void*)( *(long*)( get_pred(bp) ) ) );
      remove_block( (void*)( *(long*)( get_succ(bp) ) ) );
      bp = PREV_BLKP(bp);
      add_block(bp);
    }
    return bp;
}

void free (void *ptr) {

  REQUIRES (ptr!=NULL);
  REQUIRES ((size_t)(ptr)%8 == 0);

/* $end mmfree */
    if(ptr == 0)
        return;

/* $begin mmfree */
    size_t size = GET_SIZE(HDRP(ptr));
/* $end mmfree */
    if (heap_listp == 0){
        mm_init();
    }
/* $begin mmfree */

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}


void *realloc(void *oldptr, size_t size) {

  REQUIRES (oldptr!=NULL);
  REQUIRES ((size_t)(oldptr)%8 == 0);

  printf ("realloc %d\n",(int)size);
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    mm_free(oldptr);

    return newptr;

}


void *calloc (size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *newptr;
  printf ("calloc %d\n" ,(int)size);
  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

// extend_heap - Extend heap with free block and return its block pointer

static void *get_succ(void *bp)
{

  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

  return bp;
}

static void *get_pred(void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

  return (void*)((char*)(bp) + DSIZE);
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/*
 * place - Place block of asize bytes at start of free block bp
 and split if remainder would be at least minimum block size */


static void place(void *bp, size_t asize)
{

  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (3*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_block(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        add_block(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_block(bp);
    }

}



static void *find_fit(size_t asize)

{

/*#ifdef NEXT_FIT
    // Next fit search
    char *oldrover = rover;

    // Search from the rover to the end of list
    for ( ; rover != NULL ;
          rover = (void*)(*(long*)(get_succ(rover))))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    // search from start of list to old rover
    for (rover = root; rover < oldrover;
         rover =(void*)(*(long*)(get_succ(rover))) )
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  // no fit found
#else*/

    /* First fit search */
    void *bp;

    for (bp = root; bp != NULL ;
         bp = (void*)(*(long*)(get_succ(bp))))
        {
          printf("in first fit search \n");
          REQUIRES (bp != NULL);
          REQUIRES (((size_t)(bp))%8 == 0);
          if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            printf("got bp %p \n",(bp));
            return bp;
        }
    }
    return NULL; /* No fit */
/* $end mmfirstfit */
//#endif
}

static void printblock(void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    /* printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp,
        hsize, (halloc ? 'a' : 'f'),
        fsize, (falloc ? 'a' : 'f'));*/

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }
}

static void checkblock(void *bp)
{
    REQUIRES (bp!=NULL);
    REQUIRES ((size_t)(bp)%8 == 0);
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
  // char *bp = heap_listp;

  if (verbose)
    printf("Heap (%p):\n", heap_listp);

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  long *list;
  for (list = root; list != NULL;
       list = (void*)(*(long*)( get_succ(list) )) ) {
    printf("here\n");
    if (verbose)
      printblock(list);
    checkblock(list);
  }

  char *bp;

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)
      {
        printblock(bp);
        checkblock(bp);
      }
  }

  if (verbose)
    printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
      {
        printf("Bad epilogue header\n");
        if (GET_SIZE(HDRP(bp)) != 0)
          printf ("size is not 0\n");
        if (!(GET_ALLOC(HDRP(bp))) )
          printf ("not allocated properly\n");
     }
    return 0;
}

/*** explicit list manipulation functions ***/

static void add_block(void *bp)
{
  REQUIRES (*(long*)bp != 0) ;
  REQUIRES ((size_t)(bp) % 8 == 0);
  if (root == 0)
    {
      root = bp;
      long *succ = get_succ(bp);
      long *pred = get_pred(bp);
      *succ = 0;
      *pred = 0;
    }
  else
    {
      long *succ = (long*)get_succ(bp);
      long *pred = (long*)get_pred(bp);
      *(pred) = 0;
      *(succ) = (long)(root);
      long *root_pred = (long*)get_pred(root);
      *(root_pred) = (long)(bp);
      root = bp;
    }
  return;
}

static void remove_block(void *bp)
{
  REQUIRES ( *(long*)(bp) != 0);
  REQUIRES ( (size_t)(bp) % 8 == 0);

  long *pred = (long*)get_pred(bp);
  long *succ = (long*)get_succ(bp);

  if ( *pred == 0 && *succ != 0)
    //block to be removedd is the first block in the list
    {
      long *new_block_pred = (long*)get_pred( (void*)(succ) );
      *new_block_pred = 0;
      root = succ;
      return;
    }
  else if (*pred != 0 && *succ == 0)
    //block to be removed is the last block in the list
    {
      long *new_block_succ = (long*)get_succ( (void*)(pred) );
      *new_block_succ = 0;
      return;
    }
  else if (*pred != 0 && *succ != 0)
    //block to bre removed is located somewhere within the list.
    {
      long *before_block_succ = (long*) get_succ( (void*)(*pred) );
      *before_block_succ = *succ;

      long *after_block_pred = (long*) get_pred( (void*)(*succ) );
      *after_block_pred = *pred;

      return;
    }

  else if ( *pred == 0 && *succ == 0)
    {
      root = 0;
    }
}
