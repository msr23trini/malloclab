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
#include <limits.h>
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
static void print_list();

static void *first_best_fit (void *bp, size_t asize, size_t diff);

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (312)  /* Extend heap by this amount (bytes) */

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

#define SET_SUCC(bp) ( *(long*)bp)

#define SET_PRED(bp) ( * ((long*)bp +1 ))

/* Global variables */
 char *heap_listp = 0;  /* Pointer to first block */
 void *root ; //pointer to first free address
#ifdef NEXT_FIT
 void *rover;           /* Next fit rover */
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
  //printf("in mm_init \n");
  if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
    return -1;
  root = (void*)heap_listp;
  SET_SUCC(root) = 0;
  PUT(heap_listp + (2*WSIZE), 0);              /* Alignment padding */
  PUT(heap_listp + (3*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (4*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (5*WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_listp += (4*WSIZE);

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;

#ifdef NEXT_FIT
    rover = root;
#endif

    //mm_checkheap(1);
    print_list();
    return 0;
}


void *malloc (size_t size) {
  //mm_checkheap(1);  // Let's make sure the heap is ok!
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;

    //printf ("malloc %d\n" ,(int)size);
    if (heap_listp == 0 ){
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

    if ((bp = find_fit(asize)) != NULL) {
      place(bp, asize);
      ENSURES ( (size_t)(bp)%8 == 0);
      //printf("returning from malloc\n");
      return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    //printf ("resizing the heap \n");
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    REQUIRES (bp!=NULL);
    REQUIRES ((size_t)(bp)%8 == 0);
    place(bp, asize);
    //printf("returning from malloc\n");
    return bp;
}



// coalesce - Boundary tag coalescing. Return ptr to coalesced block

static void *coalesce(void *bp)
{
  //printf ("in coalesce\n");
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);
  //mm_checkheap(1);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    //printf("coalescing");
    //Case 1 - both allocated
    if (prev_alloc && next_alloc) {
      //printf ("case 1 \n ") ;
      add_block(bp);

    }

    //Case 3 - prev allocated but next block is free
    else if (prev_alloc && !next_alloc) {
      // printf ("case 3 \n");

      remove_block( NEXT_BLKP(bp) );
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      PUT(HDRP(bp), PACK(size, 0));
      PUT(FTRP(bp), PACK(size,0));
      add_block(bp);
    }

    //Case 2 - prev is free but  next is allocated
    else if (!prev_alloc && next_alloc) {
      //printf ("case 2 \n");
      //printf ( "case 2 bp %p \n",bp);
      //printf (" prev bp %p %d \n", PREV_BLKP(bp), GET_SIZE((HDRP(PREV_BLKP(bp)))));

      remove_block( PREV_BLKP(bp) );
      size += GET_SIZE(HDRP(PREV_BLKP(bp)));
      PUT(FTRP(bp), PACK(size, 0));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      bp = PREV_BLKP(bp);
      add_block(bp);

      //printf (" root %p \n", (void*)root);
       //printf (" bp %p \n", bp);
       //void *next_node = (void*)(*(long*)get_succ(void*)root));
       //void *next_next_node =  (void*)(*(long*)get_succ(next_node));

       //printf (" next node %p \n", next_node );
       //printf (" next next node %p \n", next_next_node );

    }

    // Case 4 - both prev and next are free
    else {
      //printf ("case 4 \n");
      remove_block( PREV_BLKP(bp) );
      remove_block( NEXT_BLKP(bp) );
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

      bp = PREV_BLKP(bp);
      add_block(bp);
    }
    ENSURES ( (size_t)(bp)%8 == 0);
    //printf ("returning from coalesce\n");
    return bp;
}

void free (void *ptr) {
  //printf("in free\n");
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
    //printf("reuturning from free\n");
}


void *realloc(void *oldptr, size_t size) {

  REQUIRES (oldptr!=NULL);
  REQUIRES ((size_t)(oldptr)%8 == 0);

  //printf ("realloc %d\n",(int)size);
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
    ENSURES ( (size_t)(newptr)%8 == 0);
    return newptr;

}


void *calloc (size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *newptr;
  //printf ("calloc %d\n" ,(int)size);
  newptr = malloc(bytes);
  memset(newptr, 0, bytes);
  ENSURES ( (size_t)(newptr)%8 == 0);
  return newptr;
}



static void *get_succ(void *bp)
{
  //printf ("root %p \n",(void*)root);
  //printf ("getting successor of %p\n",bp);
  REQUIRES (bp != NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

  bp = (void*)(*(long*)bp);
  if (bp == NULL)
    return NULL;
  else{
    //rintf ("successor = %p",bp);
    return bp;
  }
}

static void *get_pred(void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

  bp = (void*)((char*)(bp) + DSIZE);
  bp = (void*)(*(long*)(bp));

  ENSURES ( (size_t)(bp)%8 == 0);

  if (bp == NULL)
    return NULL;
  else
    return bp;
}

static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    //printf("size %d\n",(int)(size));
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce((void*)bp);
}


/*
 * place - Place block of asize bytes at start of free block bp
 and split if remainder would be at least minimum block size */


static void place(void *bp, size_t asize)
{
  //printf ("in place \n");
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (3*DSIZE)) {
      //printf("needs to split block\n");
      remove_block (bp);
      PUT(HDRP(bp), PACK(asize, 1));
      PUT(FTRP(bp), PACK(asize, 1));

      bp = NEXT_BLKP(bp);
      //printf ("setting bp to next block %p\n", bp);
      //printf ("ready to add block\n");
      PUT(HDRP(bp), PACK(csize-asize, 0));
      //printf ("added header\n");
      PUT(FTRP(bp), PACK(csize-asize, 0));
      //printf ("added footer \n");
      add_block(bp);

    }
    else {
      //printf("no need to split block\n");
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_block(bp);
    }
    //printf ("returning from place \n");
}

static void *first_best_fit (void *bp, size_t asize, size_t diff)
{


  for (size_t i = 0; i < 3;i++)
    {
      void *next_bp = get_succ(bp);
      if (next_bp == NULL)
        break;

      size_t size =  GET_SIZE(HDRP((void*)(next_bp)));
      int alloc = GET_ALLOC( HDRP( (void*)(next_bp) ));
      if ( (asize <= size) &&  !alloc
           && (size - asize) < diff)
        {
          ENSURES ( (size_t)(bp)%8 == 0);
          bp = next_bp;
          diff = size - asize;
        }
    }
  return bp;
}


static void *find_fit(size_t asize)

{
   /* First fit search */
  void* bp;

  //printf("in find fit\n");
    // printf ("root = %p\n",(void*)(root));
    //printf ("last byte = %p \n", mem_heap_hi());
    //printf ("root successor %p\n", (void*)(*root));
    //printf ("next %p", get_succ(root));
    print_list();
    for (bp =(void*)( *(long*)root); bp != NULL ;
         bp = get_succ((void*)bp) )
        {
          //printf("in first fit search np = %p \n",(void*)bp);
          REQUIRES ((void*)bp != NULL);
          REQUIRES (((size_t)(bp))%8 == 0);
          size_t size =  GET_SIZE(HDRP((void*)(bp)));
          if (!GET_ALLOC( HDRP( (void*)(bp) ) ) &&
              (asize <= size))
            {

              ENSURES ( (size_t)(bp)%8 == 0);
              size_t diff = size - asize;
              return first_best_fit((void*)bp,asize, diff) ;
            }
    }
    return NULL; /* No fit */

}

static void printblock(void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);
  size_t hsize, halloc, fsize, falloc;

  // checkheap(0);
  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  /*printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
          (int)hsize, (halloc ? 'a' : 'f'),
          (int)fsize, (falloc ? 'a' : 'f'));*/

  if (hsize == 0) {
    // printf("%p: EOL\n", bp);
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
    //printf("Heap (%p):\n", heap_listp);

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  long *list;
  for (list = root; list != NULL;
       list =  get_succ(list)  ) {
    //printf("here\n");
    if (verbose)
      //printblock(list);
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
        //printf("Bad epilogue header\n");
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
  //printf ("adding block\n");
  REQUIRES ( bp != NULL ) ;
  REQUIRES ((size_t)(bp) % 8 == 0);


  //printf ("adding to the beginning of the list \n");
  //printf ("root %p \n",root);
  //printf ("root val %d ",*(int*)

  if ( (*(long*)root != 0))
       SET_PRED(*(long*)root) = (long)(bp);
  SET_SUCC(bp) = *(long*)root;
  SET_PRED(bp) = 0;
  SET_SUCC(root) = (long)(bp);
  //print_list();

  //printf("returned from adding block\n");
  return;
}

static void remove_block(void *bp)
{
  //printf ("remove block\n");
  REQUIRES ( bp != NULL );
  REQUIRES ( (size_t)(bp) % 8 == 0);

  void *pred = get_pred(bp);
  void *succ = get_succ(bp);

  if ( pred == NULL && succ != NULL)
    //block to be removed is the first block in the list
    {
      SET_SUCC(bp) = 0;
      SET_PRED(succ) = 0;
      SET_SUCC(root) = (long)(succ);

    }
  else if (pred != NULL && succ == NULL)
    //block to be removed is the last block in the list
    {
      SET_SUCC(pred) = 0;
      SET_PRED(bp) = 0;

    }

  else if (pred != NULL && succ != NULL)
    //block to be removed is located somewhere within the list.
    {
      SET_SUCC(pred) = (long)(succ);
      SET_PRED(succ) = (long)(pred);
      SET_PRED(bp) = 0;
      SET_SUCC(bp) = 0;

    }

  else if ( pred == NULL && succ == NULL)
    {
      //printf("resetting root\n");
      SET_SUCC(root) = 0;
    }
  //print_list();
  return;
}

static void print_list()
{
  //void* bp;

  /*for ( bp =root ;bp!= NULL ;bp=get_succ(bp))
    {
      // printf ("hello \n");
      //printblock(bp);


      }*/
  return;

}

