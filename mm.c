/*
 * mm.c
 * Shastri Ram- shastrir
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
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
static void swap(void *prev, void *next, void *bp);
static void swap4( void *prev_block, void *next_block);
static void make_new_first_block( void *next, void *prev);
static void normal_swap(void *next, void *prev);
static void clear_first(void *bp);
static void new_first_block_2(void *next, void *prev);
static void new_connection( void *prev, void *next);
static void update_link_1(void *next, void *prev, void *bp) ;
static void update_link_2(void *next, void *prev, void *bp);

/* $begin mallocmacros */
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



/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static long *explicit_list = 0 ; //pointer to first free address
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
  /* $end mminit */


  /* $begin mminit */

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;

#ifdef NEXT_FIT
    rover = explicit_list;
#endif

    //mm_checkheap(1);
  return 0;
}


/*
 * malloc
 */
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

static void move_to_root(void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

  void *succ = get_succ(bp);
  void **pred = get_pred(bp);
  if ( *pred  == NULL ) //already at the root
    return;
  *(long*)(succ)  = (long)(explicit_list);
  void* next_pred  = get_pred(explicit_list);
  *(long*)(next_pred) = (long)(bp);
  explicit_list = bp;
  *pred = NULL ;
  return;
}


static void swap(void *prev, void *next, void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

  REQUIRES (prev!=NULL);
  REQUIRES ((size_t)(prev)%8 == 0);

  REQUIRES (prev!=NULL);
  REQUIRES ((size_t)(prev)%8 == 0);


  if ( (prev == NULL) && (next !=  NULL) )
    //first block in list. predecessor but no successor.
    {
      *(long*)(next) = *(long*)(prev);
      void **prev_pt = (void*)(*(long*)(prev));
      *prev_pt = NULL;
      void *prev_pt_succ = get_succ(prev_pt);
      *(long*)(prev_pt_succ) = (long)(explicit_list);
      void *explicit_list_pred = get_pred(explicit_list);
      *(long*)(explicit_list_pred)= (long)(prev_pt);
      explicit_list = bp;
      return;
    }
  else if  ( (prev!= NULL) && (next == NULL) )
    //last block in list.remains last block in the list.
    {
      return;
    }
  else if  ((prev != NULL) && (next != NULL) )
    {
      void *succ = get_succ((void*)(*(long*)(prev)));
      *(int*)(succ) = *(int*)(next);
      void *pred = get_pred((void*)(*(long*)(next)));
      *(int*)(pred) =*(int*)(prev);
      return;
    }
}
/* $end mmfree */
/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp)
{
  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);
  //mm_checkheap(1);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //both allocated
    if (prev_alloc && next_alloc) {            /* Case 1 */
      printf("case 1/n");
      if ( explicit_list == 0)
        {
          REQUIRES (explicit_list == 0);
          explicit_list = bp;
          void **succ =  get_succ(bp);
          void **pred =  get_pred(bp);
          *succ = NULL;
          *pred = NULL;
        }
      else
        {
          REQUIRES (explicit_list != 0);
          move_to_root(bp);
        }
      return bp;
    }

    //prev allocated but next block is free
    else if (prev_alloc && !next_alloc) {      /* Case 3 */
      printf("case 3/n");
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        swap(  get_pred(NEXT_BLKP(bp)), get_succ(NEXT_BLKP(bp)), bp );
        move_to_root(bp);


    }

    //prev is free but  next is allocated
    else if (!prev_alloc && next_alloc) {      /* Case 2 */
      printf ("case 2/n");
      size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        swap(  get_pred(bp), get_succ(bp), bp );

        move_to_root(bp);
    }

    //both prev and next are free
    else {                                     /* Case 4 */
      printf("case 4/n");
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        swap4( PREV_BLKP(bp),NEXT_BLKP(bp) );
        bp = PREV_BLKP(bp);
         move_to_root(bp);
    }
    return bp;
}

static void swap4( void *prev_block, void *next_block)
{

  REQUIRES (prev_block!=NULL);
  REQUIRES ((size_t)(prev_block)%8 == 0);

  REQUIRES (next_block!=NULL);
  REQUIRES ((size_t)(next_block)%8 == 0);

  bool prev_is_last, prev_is_first, next_is_last, next_is_first,
    next_is_normal, prev_is_normal = false;

  void *prev_block_succ = get_succ(prev_block);
  void *prev_block_pred = get_pred (prev_block);

  void *next_block_succ = get_succ(next_block);
  void *next_block_pred = get_pred(next_block);

  if (prev_block_pred == NULL)
    prev_is_last = true;
  if (prev_block_succ == NULL)
    prev_is_first = true;
  if (next_block_pred == NULL)
    next_is_last = true;
  if (next_block_succ == NULL)
    next_is_first = true;
  if (next_block_succ != NULL && next_block_pred != NULL)
    next_is_normal = true;
  if (prev_block_succ != NULL && prev_block_pred != NULL)
    prev_is_normal = true;

  //previous block is the last block in the list and the next block
  //is the first block in the list.
  if (prev_is_last && next_is_first)
    {
      void *next_block_pred_pt = (void*)(*(long*)(next_block_pred));
      void *prev_block_succ_pt = (void*)(*(long*)(prev_block_succ));
      make_new_first_block( next_block_pred_pt, prev_block_succ_pt);
      *(long*)(prev_block_succ) = (long)( next_block_pred_pt);
      return;
    }

  //prev block is the last block in the list and the next block is
  //somewhere within the list.
  else if ( prev_is_last && next_is_normal)
    {
      normal_swap(next_block_succ, next_block_pred);
      return;
    }

  //prev block is the first block and the next block is the last block
  else if (prev_is_first && next_is_last)
    {
      explicit_list = prev_block;
      void *prev_block_pred_pt = (void*)(*(long*)(prev_block_pred));
      void *next_block_succ_pt = (void*)(*(long*)(next_block_succ));
      new_first_block_2(next_block_succ_pt, prev_block_pred_pt);
      return;
    }

  //prev block is first and next block is somewhere within the list
  else if (prev_is_first && next_is_normal)
    {
      normal_swap(next_block_succ, next_block_pred);
      clear_first(prev_block);
      move_to_root(prev_block);
      return;
    }

  //both prev and next are located within the list
  else if (prev_is_normal && next_is_normal)
    {
      normal_swap(next_block_succ, next_block_pred);
      normal_swap(prev_block_succ, prev_block_pred);
      return;
    }

  //prev is within the list and next is the last block
  else if (prev_is_normal && next_is_last)
    {
      explicit_list = prev_block;
      void *explicit_list_pred = get_pred(explicit_list);
      explicit_list_pred = NULL;
      void *prev_block_pred_pt = (void*)(*(long*)(prev_block_pred));
      void *next_block_succ_pt = (void*)(*(long*)(next_block_succ));
      new_connection(prev_block_pred_pt, next_block_succ_pt);
      return;
    }

  //prev is within the list and next is the first block
  else if (prev_is_normal && next_is_first)
    {
      clear_first(next_block);
      void *prev_block_succ_pt = (void*)(*(long*)(prev_block_succ));
      void *prev_block_pred_pt = (void*)(*(long*)(prev_block_pred));
      normal_swap(prev_block_succ_pt, prev_block_pred_pt);
      move_to_root(prev_block);
      return;
    }
}

static void new_connection( void *prev, void *next)
{
  REQUIRES (prev!=NULL);
  REQUIRES ((size_t)(prev)%8 == 0);

  REQUIRES (next !=NULL);
  REQUIRES ((size_t)(next)%8 == 0) ;

  void *prev_succ = get_succ(prev);
  *(long*)(prev_succ) = (long)(next);

  void *next_pred = get_pred(next);
  *(long*)(next_pred) = (long)(prev);
  return;
}

static void clear_first(void *bp)
{

  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

  void **succ = get_succ(bp);
  *succ = NULL;
  return;
}

static void new_first_block_2(void *next, void *prev)
{

  REQUIRES (prev!=NULL);
  REQUIRES ((size_t)(prev)%8 == 0);

  REQUIRES (next !=NULL);
  REQUIRES ((size_t)(next)%8 == 0);

  void *next_pred = get_pred(next);
  *(long*)(next_pred) = (long)(explicit_list);

  void *explicit_list_succ = get_succ(explicit_list);
  *(long*)(explicit_list_succ) = (long)(next);

  clear_first(prev);

  return;
}


static void normal_swap(void *next, void *prev)
{

  REQUIRES (prev!=NULL);
  REQUIRES ((size_t)(prev)%8 == 0);

  REQUIRES (next !=NULL);
  REQUIRES ((size_t)(next)%8 == 0);

  void *succ = get_succ((void*)(*(long*)(prev)));
  *(int*)(succ) = *(int*)(next);
  void *pred = get_pred( (void*)(*(long*)(next)) );
  *(int*)(pred) =*(int*)(prev);
  return;
}

static void make_new_first_block( void *next, void *prev)
{
  REQUIRES (prev!=NULL);
  REQUIRES ((size_t)(prev)%8 == 0);

  REQUIRES (next !=NULL);
  REQUIRES ((size_t)(next)%8 == 0);

  void **next_succ = get_succ(next);
  *next_succ = NULL;

  void *next_pred = get_pred(next);
  *(long*)(next_pred) = (long)(prev);

  void *prev_pred = get_pred(prev);
  *(long*)(prev_pred) = (long)(next);

  return;
}

/*
 * free
 */
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

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
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
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */

static void place(void *bp, size_t asize)
     /* $end mmplace-proto */
{

  REQUIRES (bp!=NULL);
  REQUIRES ((size_t)(bp)%8 == 0);

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (3*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        update_link_2(get_succ(bp), get_pred(bp), bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        update_link_1(get_succ(bp), get_pred(bp), bp);
    }

}

static void update_link_1(void *next, void *prev, void *bp)
{
  bool last_byte;
  if ( NEXT_BLKP(bp) == mem_heap_hi() )
    last_byte = true; //block has last byte
  if ( next == NULL && prev == NULL)
    //block was the only block in the explicit list
    {
      if (last_byte)
        {
          explicit_list = 0;
          return;
        }
      else
        {
          bp = NEXT_BLKP(bp);
          void **succ = get_succ(bp);
          void **pred = get_pred(bp);
          *succ = NULL;
          *pred = NULL;
          explicit_list = bp;
          return;
        }
    }
  else if (next == NULL && prev != NULL)
    //allocated block is the first block in the explicit list
    {
      void *prev_bp = (void*)(*(long*)(prev));
      void **succ = get_succ(prev_bp);
      *succ = NULL;
      return;
    }
  else if (next != NULL && prev == NULL)
    //allocated block is the last block in the explicit list
    {
      void *next_pt = (void*)(*(long*)(next));
      void **pred = get_pred(next_pt);
      *pred = NULL;
      explicit_list = next_pt;
      return;
    }
  else if (next != NULL && prev !=NULL)
    //allocate block lies somewhere within the explicit list
    {
      normal_swap((void*)(*(long*)(next)), (void*)(*(long*)(prev)));
      return;
    }
}

static void update_link_2(void *next, void *prev, void *bp)
{
  bool last_byte;
  if (NEXT_BLKP(bp) == mem_heap_hi() )
     last_byte = true; //block has last byte
  if ( next == NULL && prev == NULL)
    //block was the only block in the explicit list
    {
      if (last_byte)
        {
          explicit_list = 0;
          return;
        }
      else
        {
          bp = NEXT_BLKP(bp);
          void **succ = get_succ(bp);
          void **pred = get_pred(bp);
          *succ = NULL;
          *pred = NULL;
          explicit_list = bp;
          return;
        }
    }
  else if (next == NULL && prev != NULL)
    //allocated block is the first block in the explicit list
    {
      void *new_block = NEXT_BLKP(bp);
      void **new_block_succ = get_succ(new_block);
      void *new_block_pred = get_pred(new_block);
      *new_block_succ = NULL;
      void* prev_block = (void*)(*(long*)(prev));
      *(long*)new_block_pred = (long)(prev_block);
      void *prev_block_succ = get_succ(prev_block);
      *(long*)(prev_block_succ) = (long)(new_block);
      return;
    }
  else if (next != NULL && prev == NULL)
    //allocated block is the last block in the explicit list
    {
      void *new_block = NEXT_BLKP(bp);
      void *new_block_succ = get_succ(new_block);
      void **new_block_pred = get_pred(new_block);
      *new_block_pred = NULL;
      void* next_block = (void*)(*(long*)(next));
      void *next_block_pred = get_pred(next_block);
      *(long*)(next_block_pred) = (long)(new_block);
      *(long*)(new_block_succ) = (long)(next_block);
      explicit_list = new_block;
      return;
    }
  else if (next != NULL && prev != NULL)
    {
      void *new_block = NEXT_BLKP(bp);
      void *new_block_succ = get_succ(new_block);
      void *new_block_pred = get_pred(new_block);
      void *next_pt = (void*)(*(long*)(next));
      void *prev_pt = (void*)(*(long*)(prev));
      *(long*)(new_block_succ) = (long)(next_pt);
      *(long*)(new_block_pred) = (long)(prev_pt);

      void *next_pt_pred = get_pred(next_pt);
      *(long*)(next_pt_pred) = (long)(new_block);

      void *prev_pt_succ = get_succ(prev_pt);
      *(long*)(prev_pt_succ) = (long)(new_block);

      return;
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
    for (rover = explicit_list; rover < oldrover;
         rover =(void*)(*(long*)(get_succ(rover))) )
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  // no fit found
#else*/
/* $begin mmfirstfit */
    /* First fit search */
    void *bp;

    for (bp = explicit_list; bp != NULL ;
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
  for (list = explicit_list; list != NULL;
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
