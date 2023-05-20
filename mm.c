#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "KJ_4",
    /* First member's full name */
    "HyunSoo KIM",
    /* First member's email address */
    "hsk7953@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 
 * mm_init - initialize the malloc package.
 */
 /* 매크로*/
#define WSIZE 4 // word and header footer 사이즈를 byte로. 
#define DSIZE 8 // double word size를 byte로
#define CHUNKSIZE (1<<12) // heap을 늘릴 때 얼만큼 늘릴거냐? 4kb 분량.

#define MAX(x,y) ((x)>(y)? (x) : (y)) // x,y 중 큰 값을 가진다.

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 만듬.
#define PACK(size,alloc) ((size)| (alloc)) // alloc : 가용여부 (ex. 000) / size : block size를 의미. =>합치면 온전한 주소가 나온다.

/* address p위치에 words를 read와 write를 한다. */
#define GET(p) (*(unsigned int*)(p)) // 포인터를 써서 p를 참조한다. 주소와 값(값에는 다른 블록의 주소를 담는다.)을 알 수 있다. 다른 블록을 가리키거나 이동할 때 쓸 수 있다. 
#define PUT(p,val) (*(unsigned int*)(p)=(int)(val)) // 블록의 주소를 담는다. 위치를 담아야지 나중에 헤더나 푸터를 읽어서 이동 혹은 연결할 수 있다.

// address p위치로부터 size를 읽고 field를 할당
#define GET_SIZE(p) (GET(p) & ~0x7) // '~'은 역수니까 11111000이 됨. 비트 연산하면 000 앞에거만 가져올 수 있음. 즉, 헤더에서 블록 size만 가져오겠다.
#define GET_ALLOC(p) (GET(p) & 0x1) // 00000001이 됨. 헤더에서 가용여부만 가져오겠다.

/* given block ptr bp, header와 footer의 주소를 계산*/
#define HDRP(bp) ((char*)(bp) - WSIZE) // bp가 어디에있던 상관없이 WSIZE 앞에 위치한다.
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.

/* GIVEN block ptr bp, 이전 블록과 다음 블록의 주소를 계산*/
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE))) // 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블록의 헤더 뒤로 감.)
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 그 전 블록의 bp위치로 이동.(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동.)

#define PRED_FREEP(bp) (*(void**)(bp)) // 포인터 그자체
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))  // 포인터 그 자체

static char *heap_listp;  // 처음에 쓸 큰 가용블록 힙을 만들어줌.
static char *last_bp; // 마지막으로 할당된 블록을 가리키는 포인터
// next fit 할당 방식에서 다음 할당시 검색을 시작할 위치를 정해준다.
// 이전 할당된 블록의 주소를 기억하여 다음 할당시 그 위치부터 검색 시작
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

void removeBlock(void *bp);
void putFreeBlock(void *bp);

static char *heap_listp = NULL;
static char *free_listp = NULL;  // 가용리스트의 첫 번째 블록을 가리키는 포인터
// static void *next_fit(size_t adjusted_size);
int mm_init(void)
{   // @@@@ explicit에서 추가 @@@@
    heap_listp = mem_sbrk(24);// 24byte를 늘려주고, 함수의 시작부분을 가리키는 주소를 반환,mem_brk는 끝에 가있음
    if (heap_listp == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0); //Unused padding
    PUT(heap_listp + WSIZE, PACK(16,1)); // 프롤로그 헤더 16/1
    PUT(heap_listp + 2*WSIZE,NULL); // 프롤로그 PRED 포인터 NULL로 초기화
    PUT(heap_listp + 3*WSIZE,NULL); // 프롤로그 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + 4*WSIZE,PACK(16,1)); // 프롤로그 풋터 16/1
    PUT(heap_listp + 5*WSIZE,PACK(0,1)); // 에필로그 헤더 0/1

    free_listp = heap_listp + DSIZE; // free_listp를 PRED 포인터 가리키게 초기화
    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) //word가 몇개인지 확인해서 넣으려고(DSIZE로 나눠도 됨)
        return -1;
    return 0;
}
//연결
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록이 할당되었는지 아닌지 0 or 1
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록이 할당되었는지 아닌지 0 or 1
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록 사이즈 
    // @@@@ explicit에서 추가 @@@@
    // case 1 - 가용블록이 없으면 조건을 추가할 필요 없다. 맨 밑에서 freelist에 넣어줌
    // case 2
    if(prev_alloc && !next_alloc){
        removeBlock(NEXT_BLKP(bp)); // @@@@ explicit에서 추가 @@@@
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));//header가 바뀌었으니까 size도 바뀐다!
    }
    // case 3
    else if(!prev_alloc && next_alloc){
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
        // PUT(FTRP(bp), PACK(size,0));  // @@@@ explicit에서 추가 @@@@ - 여기 다르긴함
        // PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        // bp = PREV_BLKP(bp); //bp를 prev로 옮겨줌
    }
    // case 4
    else if(!prev_alloc && !next_alloc){
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp); //bp를 prev로 옮겨줌
    }
    putFreeBlock(bp); // 연결이 된 블록을 free list 에 추가
    return bp;
}


// extend_heap은 두 가지 경우에 호출된다.
// 1. heap이 초기화될 때 다음 블록을 CHUNKSIZE만큼 미리 할당해준다.
// 2. mm_malloc이 적당한 맞춤(fit)을 찾지 못했을 때 CHUNKSIZE만큼 할당해준다.
//                        - - -
// heap을 CHUNKSIZE byte로 확장하고 초기 가용 블록을 생성한다.
// 여기까지 진행되면 할당기는 초기화를 완료하고, application으로부터
// 할당과 반환 요청을 받을 준비를 완료하였다.
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    // Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // word가 짝수면 words *WSize, 홀짝 구분
    if (((bp = mem_sbrk(size)) == (void*)-1)) //size를 불러올 수 없으면
        return NULL;
    
    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size,0)); // Free block header
    PUT(FTRP(bp), PACK(size,0)); // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // New epilogue header

    // Coalesce(연결후 합침)
    return coalesce(bp);
}
// find_fit함수, frist-fit
static void *find_fit(size_t asize){
    void *bp;
    // @@@@ explicit에서 추가 @@@@
    // 가용리스트 내부의 유일한 할당블록인 프롤로그 블록을 만나면 종료
    for(bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(GET_SIZE(HDRP(bp)) >= asize){
            return bp;
        }
    }
    return NULL; // No fit
}
//place 함수
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    //할당블록은 freelist에서 지운다
    removeBlock(bp);
    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize,1));//현재 크기를 헤더에 집어넣고
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
        putFreeBlock(bp); // free list 첫번째에 분할된 블럭을 넣는다.
    }
    else{
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; //할당할 블록 사이즈
    size_t extendsize;
    void *bp; 

    // Ignore spurious requests - size가 0이면 할당x
    if(size <= 0) // == 대신 <=
        return NULL;
    
    // Adjust block size to include overhead and alignment reqs.
    if(size <= DSIZE) // size가 8byte보다 작다면,
        asize = 2*DSIZE; // 최소블록조건인 16byte로 맞춤
    else              // size가 8byte보다 크다면
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1)) / DSIZE);

    //Search the free list for a fit - 적절한 가용(free)블록을 가용리스트에서 검색
    if((bp = find_fit(asize))!=NULL){
        place(bp,asize); //가능하면 초과부분 분할
        return bp;
    }

    //No fit found -> Get more memory and place the block
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp,asize);
    return bp;
}

// LIFO 방식으로 새로 반환되거나 생성된 가용 블록을 가용리스트 맨 앞에 추가
void putFreeBlock(void *bp){
    SUCC_FREEP(bp) = free_listp;
    PRED_FREEP(bp) = NULL;
    PRED_FREEP(free_listp) = bp;
    free_listp = bp;
}
// free list 맨 앞에 프롤로그 블록이 존재
void removeBlock(void *bp){
    // 첫 번째 블록을 없앨 때
    if(bp == free_listp){
        PRED_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }else{
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);    
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size){
    if(size <= 0){ 
        mm_free(bp);
        return 0;
    }
    if(bp == NULL){
        return mm_malloc(size); 
    }
    void *newp = mm_malloc(size); 
    if(newp == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize){
    	oldsize = size; 
	}
    // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로
    // 복사해주는 함수(bp로부터 oldsize만큼의 문자를 newp로 복사해라)
    memcpy(newp, bp, oldsize); 
    mm_free(bp);
    return newp;
}
