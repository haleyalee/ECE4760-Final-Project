/*********************************************************************
 *
 *                 NTSC TV interface
 *
 *********************************************************************
 * Bruce Land Cornell University
 * June 2014
 * This code uses many cool ideas from
 * Programming 32-bit Microcontrollers in C: Exploring the PIC32
 * by Lucio Di Jasio
 *
 * Uses two Compare units from one timer to do sync and video timing
 *~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * SCK1 is pin 25
 * SDO1 is PPS group 2, map to RPA1 (pin 3)
 * SDI1 is PPS group 2, map to RPB8 (pin 17)
 * SYNC is PortB.0 (pin 4)
 */

#include "config_1_3_2.h"
// threading library
#include "pt_cornell_1_3_2.h"
#include <plib.h>
#include <xc.h> // need for pps
#include <stdio.h>
#include <stdlib.h>
// need for rand function
#include <stdlib.h>
// fixed point types
#include <stdfix.h>
#include <math.h>
#include <time.h>
#include <conio.h>


#define EnablePullDownA(bits) CNPUACLR=bits; CNPDASET=bits;
#define DisablePullDownA(bits) CNPDACLR=bits;
#define EnablePullUpA(bits) CNPDACLR=bits; CNPUASET=bits;
#define DisablePullUpA(bits) CNPUACLR=bits;

#define EnablePullDownB(bits) CNPUBCLR=bits; CNPDBSET=bits;
#define DisablePullDownB(bits) CNPDBCLR=bits;
#define EnablePullUpB(bits) CNPDBCLR=bits; CNPUBSET=bits;
#define DisablePullUpB(bits) CNPUBCLR=bits;

#define DAC_config_chan_A 0b0011000000000000

// audio sample frequency
#define Fs 44000.0
// need this constant for setting DDS frequency
#define two32 4294967296.0 // 2^32 
// sine lookup table for DDS
#define sine_table_size 256
volatile _Accum sine_table[sine_table_size];
// phase accumulator for DDS
volatile unsigned int DDS_phase;
// phase increment to set the frequency DDS_increment = Fout*two32/Fs
// For A above middle C DDS_increment =  = 42949673 = 440.0*two32/Fs
#define Fout 261.8
volatile unsigned int DDS_increment = Fout*two32 / Fs; //42949673 ;
// waveform amplitude
volatile _Accum max_amplitude = 2000;

// waveform amplitude envelope parameters
// rise/fall time envelope 44 kHz samples
volatile unsigned int attack_time = 200, decay_time = 35000, sustain_time = 1000;
//  0<= current_amplitude < 2048
volatile _Accum current_amplitude;
// amplitude change per sample during attack and decay
// no change during sustain
volatile _Accum attack_inc, decay_inc;


// phase accumulator for DDS
volatile unsigned int FM_DDS_phase;
// phase increment to set the frequency DDS_increment = Fout*two32/Fs
// For A above middle C DDS_increment =  = 42949673 = 440.0*two32/Fs
#define FM_Fout 1.8*261.8
volatile unsigned int FM_DDS_increment = FM_Fout*two32 / Fs; //42949673 ;
// waveform amplitude
volatile _Accum FM_max_amplitude = 2000, FM_out;

// waveform amplitude envelope parameters
// rise/fall time envelope 44 kHz samples
volatile unsigned int FM_attack_time = 100, FM_decay_time = 20000, FM_sustain_time = 1000;
//  0<= current_amplitude < 2048
volatile _Accum FM_current_amplitude;
// amplitude change per sample during attack and decay
// no change during sustain
volatile _Accum FM_attack_inc, FM_decay_inc;
volatile unsigned int FM_data_A;

static struct pt pt_timer, pt_color, pt_anim, pt_adc, pt_serial, pt_button;

static struct car {
    float xPos;
    float yPos;
    float xVel;
    float yVel;
    float accel;
    int flash;
};

static struct obstacle {
    float xPos;
    float yPos;
    int valid;
};

#pragma config FNOSC = FRCPLL, POSCMOD = HS, FPLLIDIV = DIV_2, FPLLMUL = MUL_15, FPBDIV = DIV_2, FPLLODIV = DIV_1
#pragma config FWDTEN = OFF
#pragma config FSOSCEN = OFF, JTAGEN = OFF
// core frequency we're running at // peripherals at 40 MHz
#define	SYS_FREQ 60000000

// The SPI channel
volatile SpiChannel spiChn = SPI_CHANNEL1; // the SPI channel to use
volatile int spiClkDiv = 6; //5 MHz pixel rate => 256 points in 51.2 microSec

// main screen buffer array 256 wide x 200 high = 51200 pixels
// 51200/32 = 1600 integer words
int screen_buffer[1600];
volatile int *screen_buffer_addr = screen_buffer;
volatile int *screen_ptr;
volatile unsigned int DAC_data_A, DAC_data_B, DAC_data; // output values
volatile unsigned int song_time, note_time;
volatile unsigned int hold_time = 0;
volatile unsigned int hold_play_time = 0;
volatile unsigned int rest = 0;
volatile int sound = 0;
static int finishSound = 0;
static int life = 9; 

// The DMA channels
#define DMAchn1 1
#define DMApri0 0

// video timing
#define line_cycles 1905 // 63.5 uSec at 30 MHz Fpb, prescaler=1
#define us_5_cycles 150 // 5 uSec at 30 MHz Fpb, prescaler=1
#define us_13_cycles 390 // beginning of the video DMA burst -- use for centering
#define us_11_cycles 330 // beginning of the video DMA burst -- use for centering
#define us_10_cycles 300 // beginning of the video DMA burst -- use for centering

#define float2Accum(a) ((_Accum)(a))
#define Accum2float(a) ((float)(a))
#define int2Accum(a) ((_Accum)(a))
#define Accum2int(a) ((int)(a))
#define float2Int(a) ((int)(a+1))

// video active lines -- 200 total
#define image_start 20
#define image_end image_start+200

// Current line number which is modified
// by a state machine in the timer2 ISR
volatile int LineCount = 0;
// ISR driven 1/60 second time
volatile int time_tick_60_hz = 0;


// video formatiing variables
//One bit masks for each bit of an INT
unsigned int pos[32] = {0x80000000, 0x40000000, 0x20000000, 0x10000000, 0x08000000, 0x04000000, 0x02000000, 0x01000000,
    0x800000, 0x400000, 0x200000, 0x100000, 0x080000, 0x040000, 0x020000, 0x010000,
    0x8000, 0x4000, 0x2000, 0x1000, 0x0800, 0x0400, 0x0200, 0x0100,
    0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01};

#include "ascii_characters.h"

#define top 0
#define left 0
#define right 255
#define bottom 199

// box obstacles at different x positions
//                    far    middle   middle   far
//                    left    left    right   right
volatile int obsPos[] = {88, 111, 134, 157};


//=== fixed conversion macros =========================================
// for 16.16 fixed point
typedef signed int fix;
#define int2fix(a)   (((fix)(a))<<16)            //Convert char to fix. a is a char
#define fix2int(a)   ((signed int)((a)>>16))    //Convert fix to int. a is an int
#define float2fix(a) ((fix)((a)*65536.0))         //Convert float to fix. a is a float
#define fix2float(a) (((float)(a))/65536.0)       //Convert fix to float. a is an int
//#define multfix(a,b) ((fix)(((( signed long long)(a))*(( signed long long)(b)))>>16)) //multiply two fixed 16.16
#define multfix(a,b) ((fix)(((( signed long)(a))*(( signed long)(b)))>>16)) //multiply two fixed 16.16
#define n 4

// Initialize car and obstacle structs
static struct car carVals;
static struct obstacle obVals[n];

void __ISR(14, ipl3) OC3Handler(void) // 14
{
    // mPORTBSetBits(BIT_1);
    // Convert DMA to SPI control 
    DmaChnSetEventControl(DMAchn1, DMA_EV_START_IRQ(_SPI1_TX_IRQ)); //
    // clear the timer interrupt flag -- name from
    // http://people.ece.cornell.edu/land/courses/ece4760/PIC32/Microchip_stuff/32-bit-Peripheral-Library-Guide.pdf
    // Table 8.2
    mOC3ClearIntFlag();
    // mPORTBClearBits(BIT_1);  // for profiling the ISR execution time
}

static PT_THREAD(protothread_timer(struct pt *pt)) {
    PT_BEGIN(pt);

    static int numballs, b, i;
    static int start;
    static _Accum Accum_rand_x2, Accum_rand_y2;
    static int flip;
    static int time;

    sound = 1;
    while (1) {
        while (time == time_tick_60_hz) {
        };
        time = time_tick_60_hz;
        for (i = 0; i < 3000; i++) {
            if (i % 100 == 0) {
                flip = 1 - flip;
            }
            video_car((int) carVals.xPos, (int) carVals.yPos, flip);
            //        PT_YIELD_TIME_msec(100);
        }
        break;
    }
        sound = 0;

    PT_EXIT(pt);
    // NEVER exit while
    PT_END(pt);
} // END WHILE(1)

//Insert threads here

static PT_THREAD(protothread_anim(struct pt *pt)) {
    PT_BEGIN(pt);
    static float totalDist = 0;
    static char cmd[30];
    static float value;
    static int begin_time;
    static int finish_dist = 15;
    static int adc_4;
    static int i, j;
    static int k;
    static int finish = 0;
    static int adc_9;
    static int adc_prev;
    static int adc_start;
    static int turning = 0;
    static int randNum = 0;
    static int randNum2 = 0;
    static int objCount;
    static int resetFlag = 0;
    char words[10] = "Final time is:";
    char score[10];
    char lives[10];
    char gameOverString[10] = "Game Over";
    char cu1[] = "Cornell  ECE 4760 -- PIC32 Racing Game";
    int timeTotal = 0;
    adc_start = ReadADC10(0);
    static int adc_5;
    static int gameOver = 0;

    AcquireADC10();
    int time;
    carVals.xPos = 90;
    carVals.yPos = 175;
    carVals.xVel = 0;
    carVals.yVel = 0;
    obVals[0].xPos = obsPos[0];
    obVals[1].xPos = obsPos[1];
    obVals[2].xPos = obsPos[2];
    obVals[3].xPos = obsPos[3];
    for (i = 0; i < n; i++) {
        obVals[i].yPos = 15;
    }
    EnablePullUpB(BIT_1);
    mPORTBSetPinsDigitalIn(BIT_1);

    EnablePullDownB(BIT_4);
    mPORTBSetPinsDigitalIn(BIT_4);
    srand(PT_GET_TIME());
    while (1) {
        while (time == time_tick_60_hz) {
        };

        time = time_tick_60_hz;
        timeTotal += 1;
        totalDist += carVals.yVel / 60;
        resetFlag = mPORTBReadBits(BIT_4);
        if (resetFlag == 0) {
            gameOver = 0;
            life = 9;
            finish = 0;
            timeTotal = 0;
            totalDist = 0;
            finish_dist = 15;
            carVals.yVel = 0;
            carVals.xVel = 0;
            carVals.xPos = 90;
            carVals.yPos = 175;
            for (i = 0; i < n; i++) {
                obVals[i].valid = 0;
                obVals[i].yPos = 15;
            }
            video_clear();
            main();
            break;
        }

        if (totalDist > 300) {
            finish = 1;
        }
        if (life==0){
            finish = 1;
            gameOver = 1;
            
        }
        //else{
        randNum = rand();
        randNum2 = rand();
        if (randNum % 100 == 0) {
            randNum2 = randNum2 % 4;
            while (obVals[randNum2].valid == 1 && objCount < 3) {
                randNum2 = rand();
                randNum2 = randNum2 % 4;
            }

            obVals[randNum2].valid = 1;
            objCount += 1;
        }

        // draw left side grass
        for (i = 5; i < 78; i = i + 10) {
            for (j = 15; j < 199; j = j + 8) {
                video_grass(i, j);
            }
        }
        // draw right side grass
        for (i = 175; i < 255; i = i + 10) {
            for (j = 15; j < 199; j = j + 8) {
                video_grass(i, j);
            }
        }
        video_fill (235,180, 250, 195, 0);
        sprintf(lives, "%d", life);
        video_string (242,185, lives);

        video_car(float2Int(carVals.xPos), float2Int(carVals.yPos), 0);
        //carVals.xVel++;
        //carVals.xPos += carVals.xVel;

        // acceleration potentiometer
        // pedal pressed all the way down = 1.2 V
        adc_5 = ReadADC10(2);
        adc_4 = ReadADC10(1);
        carVals.accel = (adc_5 * .0005 - 0.08) - (adc_4 * 0.0005 - 0.06);
        
        if (finish == 1) {
            if (gameOver==0){
            video_line(82, finish_dist, 172, finish_dist, 0);
            video_line(82, finish_dist + 1, 172, finish_dist + 1, 0);
            video_line(82, finish_dist + 2, 172, finish_dist + 2, 0);
            video_line(82, finish_dist + 3, 172, finish_dist + 3, 0);
            video_line(82, finish_dist + 4, 172, finish_dist + 4, 0);
            finish_dist = finish_dist + 1;
            video_line(82, finish_dist, 172, finish_dist, 1);
            video_line(82, finish_dist + 1, 172, finish_dist + 1, 1);
            video_line(82, finish_dist + 2, 172, finish_dist + 2, 1);
            video_line(82, finish_dist + 3, 172, finish_dist + 3, 1);
            video_line(82, finish_dist + 4, 172, finish_dist + 4, 1);
            if (finish_dist > carVals.yPos - 7 ) {
                timeTotal = timeTotal / 60 + 1;
                finishSound = 1;
                PT_SPAWN(pt, &pt_timer, protothread_timer(&pt_timer));
                finishSound = 0;
                video_clear();
                while (1) {
                    sprintf(score, "%d", timeTotal);
                    video_string(100, top + 80, words);
                    video_string(130, top + 110, score);
                    resetFlag = mPORTBReadBits(BIT_4);

                    if (resetFlag == 0) {
                        gameOver = 0;
                        life = 9;
                        finish = 0;
                        timeTotal = 0;
                        totalDist = 0;
                        finish_dist = 15;
                        carVals.yVel = 0;
                        carVals.xVel = 0;
                        carVals.xPos = 90;
                        carVals.yPos = 175;
                        for (i = 0; i < n; i++) {
                            obVals[i].valid = 0;
                            obVals[i].yPos = 15;
                           }
                        video_clear();
                        main();
                        break;
                    }
                }
            }
            }
            if (gameOver==1){
                finishSound = -1;
                PT_SPAWN(pt, &pt_timer, protothread_timer(&pt_timer));
                finishSound = 0;
                video_clear();
                while (1) {
                    video_string(100,top+80, gameOverString);
                    resetFlag = mPORTBReadBits(BIT_4);

                    if (resetFlag == 0) {
                        gameOver = 0;
                        life = 9;
                        finish = 0;
                        timeTotal = 0;
                        totalDist = 0;
                        finish_dist = 15;
                        carVals.yVel = 0;
                        carVals.xVel = 0;
                        carVals.xPos = 90;
                        carVals.yPos = 175;
                        for (i = 0; i < n; i++) {
                            obVals[i].valid = 0;
                            obVals[i].yPos = 15;
                           }
                        video_clear();
                        main();
                        break;
                    }
                }
            }
                
        }




        // brake potentiometer
        adc_prev = adc_9;
        adc_9 = ReadADC10(0);
        turning = mPORTBReadBits(BIT_1);
        if (turning == 0) {
            if (adc_9 < 75)
                carVals.xVel = -1;
            else if (adc_9 > 150)
                carVals.xVel = 1;
        } else
            carVals.xVel = 0;
        if (carVals.xPos < 15)
            carVals.xPos = 15;
        if (carVals.xPos > 240)
            carVals.xPos = 240;

        if (carVals.yPos < 29) // 15 for top border, 14 to reach top of car
            carVals.yPos = 29;

        // slow down in grass
        if (((int) carVals.xPos < 78) || ((int) carVals.xPos > 175)) {
            carVals.accel = carVals.accel - 0.1;
        }

        carVals.yVel += 4 * carVals.accel;
        if (carVals.yVel > 9)
            carVals.yVel = 9;
        if (carVals.yVel < 0)
            carVals.yVel = 0;
        // update position of car
        carVals.xPos = carVals.xPos + carVals.xVel;
        carVals.yPos = carVals.yPos - 40 * carVals.accel;
        if (carVals.yPos > 180) {
            carVals.yPos = 180;
        }
        if (carVals.yPos < 40){
            carVals.yPos = 40;
        }

        // create obstacles
        for (k = 0; k < n; k++) {
            if (obVals[k].valid) {
                video_obstacle((int) obVals[k].xPos, (int) obVals[k].yPos, 0);
                obVals[k].yPos = (obVals[k].yPos + 0.4 * carVals.yVel + 0.3);
                video_obstacle((int) obVals[k].xPos, (int) obVals[k].yPos, 1);
                if (obVals[k].yPos > 185)
                    obVals[k].yPos = 185;
            }

            // collisions with obstacles
            if (((((int) carVals.yPos - 14) - ((int) obVals[k].yPos + 10)) < 0) &&
                    (((((int) carVals.xPos) - ((int) obVals[k].xPos)) > -9) && 
                    ((((int) carVals.xPos) - ((int) obVals[k].xPos + 5)) < 16)) && 
                    obVals[k].valid && 
                    ((int) carVals.yPos - (int) obVals[k].yPos > -26 && (int) carVals.yPos - (int) obVals[k].yPos < 14)) {
                life = life - 1;
                // invalidate
                obVals[k].valid = 0;
                // erase obstacle
                video_obstacle((int) obVals[k].xPos, (int) obVals[k].yPos, 0);
                obVals[k].yPos = 15;
                // slow car down
                carVals.yVel = carVals.yVel * 0.5;
                // flash car three times
                PT_SPAWN(pt, &pt_timer, protothread_timer(&pt_timer));
            }// if the car and obstacle do not collide
            else {
                if (obVals[k].yPos > 182) { // obstacle disappears at bottom of screen
                    obVals[k].valid = 0;
                    video_obstacle((int) obVals[k].xPos, (int) obVals[k].yPos, 0);
                    obVals[k].yPos = 15;
                }
            }
        }

        // border between road and grass
        video_line(82, 10, 82, 199, 1);
        video_line(172, 10, 172, 199, 1);

        // right dashed line
        video_line(104, 10, 104, 30, 1);
        video_line(104, 45, 104, 75, 1);
        video_line(104, 90, 104, 120, 1);
        video_line(104, 135, 104, 165, 1);
        video_line(104, 180, 104, 199, 1);

        // middle dashed line
        video_line(127, 10, 127, 30, 1);
        video_line(127, 45, 127, 75, 1);
        video_line(127, 90, 127, 120, 1);
        video_line(127, 135, 127, 165, 1);
        video_line(127, 180, 127, 199, 1);

        // left dashed line
        video_line(150, 10, 150, 30, 1);
        video_line(150, 45, 150, 75, 1);
        video_line(150, 90, 150, 120, 1);
        video_line(150, 135, 150, 165, 1);
        video_line(150, 180, 150, 199, 1);

        // draw car
        video_car(float2Int(carVals.xPos), float2Int(carVals.yPos), 1);
        //}
    } // END WHILE(1)
    PT_END(pt);
} // thread 3




 //==Timer 1 ISR ==========================================
void __ISR(_TIMER_4_VECTOR, ipl2) Timer4Handler(void)
{
    int junk;
    mT4ClearIntFlag();
    
    if (sound == 0){
        current_amplitude = 0;
    }else{
        current_amplitude = max_amplitude;
    }
    if (finishSound==1)
        DDS_increment = 494*two32/ Fs;
    if (finishSound==0)
        DDS_increment = 349 *two32 / Fs;
    if (finishSound==-1)
        DDS_increment = Fout * two32 /Fs;
    DDS_phase += DDS_increment;
    DAC_data = (int) (current_amplitude * sine_table[DDS_phase >> 24]) + 2048;
    
    // generate  ramp
   //  DAC_data = (DAC_data + 1) & 0xfff ; // for testing
    
    // CS low to start transaction
     mPORTBClearBits(BIT_13); // start transaction
    // test for ready
     while (TxBufFullSPI2());
     // write to spi2
     WriteSPI2(DAC_config_chan_A | (DAC_data & 0xfff));
    // test for done
    while (SPI2STATbits.SPIBUSY); // wait for end of transaction
     // CS high
     mPORTBSetBits(BIT_13); // end transaction
}





// == Timer 2 ISR =========================================

void __ISR(_TIMER_2_VECTOR, ipl2) Timer2Handler(void) {
    //mPORTBSetBits(BIT_1); // for profiling the ISR execution time
    // update the current scanline number
    LineCount++;

    // start the DMA byte blaster to the screen
    if (LineCount >= image_start && LineCount < image_end) {
        // set the Chan1 DMA transfer parameters: source & destination address,
        // source & destination size, number of bytes per event
        // 32 bytes / line with 4 bytes per transfer (SPI in 32 bit mode)
        //screen_ptr = screen_buffer + ((LineCount - image_start)<<5) ;
        DmaChnSetTxfer(DMAchn1, (void*) screen_ptr, (void*) &SPI1BUF, 32, 4, 4); //32
        // IRO 17 is the output compare 3 interrupt (See datasheet table 7.1)
        ConfigIntOC3(OC_INT_PRIOR_1 | OC_INT_ON); //3 //
        DmaChnSetEventControl(DMAchn1, DMA_EV_START_IRQ(17)); //
        // turn it on for 32 bytes
        DmaChnEnable(DMAchn1);
        // increment the image memory pointer for the next ISR pass
        screen_ptr += 8; // 8 32-bit words per line
    } else ConfigIntOC3(OC_INT_PRIOR_1 | OC_INT_OFF); //turn it off when we dont need to write to video

    // == SYNC state machine ====
    // begin long (Vertical) synch after line 247
    if (LineCount == 248) {
        OC2R = line_cycles - us_5_cycles;
    }
    // back to regular sync after line 250
    // the first condition eliminates sync for one line (to avoid duplicate)
    if (LineCount == 250) {
        OC2R = 0;
    }
    if (LineCount == 251) {
        OC2R = us_5_cycles;
    }
    // start new frame after line 262 and reset the image memory pointer and
    // update the frame time_tick
    if (LineCount == 263) {
        LineCount = 1;
        // reset for the next frame
        screen_ptr = screen_buffer_addr;
        // a general propose time base
        time_tick_60_hz++;
    }

    // clear the timer interrupt flag
    mT2ClearIntFlag();
    // mPORTBClearBits(BIT_1);  // for profiling the ISR execution time
}

//== plot a point =========================================================
//plot one point
//at x,y with color 1=white 0=black 2=invert
#define word_per_line 8

void video_pt(int x, int y, char c) {
    //each line has 18 bytes
    //calculate i based upon this and x,y
    // the word with the pixel in it
    //int i = (x/32) + y*8
    int i = (x >> 5) + y * word_per_line;
    if (c == 1)
        screen_buffer[i] = screen_buffer[i] | pos[x & 0x1f];
    else if (c == 0)
        screen_buffer[i] = screen_buffer[i] & ~pos[x & 0x1f];
    else
        screen_buffer[i] = screen_buffer[i] ^ pos[x & 0x1f];
}
// macro version
#define video_pt_m(x,y,c) \
    do{int i = (x >> 5) + y * word_per_line ; \
       if (c==1) \
	  screen_buffer[i] = screen_buffer[i] | pos[x & 0x1f];\
        else if (c==0)\
	  screen_buffer[i] = screen_buffer[i] & ~pos[x & 0x1f];\
        else\
	  screen_buffer[i] = screen_buffer[i] ^ pos[x & 0x1f];\
    } while(0);

//=============================================================================
//plot a line
//at x1,y1 to x2,y2 with color 1=white 0=black 2=invert
//NOTE: this function requires signed chars
//Code is from David Rodgers,
//"Procedural Elements of Computer Graphics",1985

void video_line(int x1, int y1, int x2, int y2, char c) {
    int e;
    signed int dx, dy, j, temp;
    signed char s1, s2, xchange;
    signed int x, y;

    x = x1;
    y = y1;

    //take absolute value
    if (x2 < x1) {
        dx = x1 - x2;
        s1 = -1;
    } else if (x2 == x1) {
        dx = 0;
        s1 = 0;
    } else {
        dx = x2 - x1;
        s1 = 1;
    }

    if (y2 < y1) {
        dy = y1 - y2;
        s2 = -1;
    } else if (y2 == y1) {
        dy = 0;
        s2 = 0;
    } else {
        dy = y2 - y1;
        s2 = 1;
    }

    xchange = 0;

    if (dy > dx) {
        temp = dx;
        dx = dy;
        dy = temp;
        xchange = 1;
    }

    e = ((int) dy << 1) - dx;

    for (j = 0; j <= dx; j++) {
        video_pt_m(x, y, c);

        if (e >= 0) {
            if (xchange == 1) x = x + s1;
            else y = y + s2;
            e = e - ((int) dx << 1);
        }

        if (xchange == 1) y = y + s2;
        else x = x + s1;

        e = e + ((int) dy << 1);
    }
}
void video_one(int x, int y) {
    video_fill(x, y, x + 3, y + 35,1);
}

void video_two(int x, int y) {
    // bottom line
    video_fill(x, y, x + 24, y + 3, 1);
    // diagonal
    video_line(x, y - 3, x + 4, y - 3, 1);
    video_line(x + 1, y - 4, x + 5, y - 4, 1);
    video_line(x + 2, y - 5, x + 6, y - 5, 1);
    video_line(x + 3, y - 6, x + 7, y - 6, 1);
    video_line(x + 4, y - 7, x + 8, y - 7, 1);
    video_line(x + 5, y - 8, x + 9, y - 8, 1);
    video_line(x + 6, y - 9, x + 10, y - 9, 1);
    video_line(x + 7, y - 10, x + 11, y - 10, 1);
    video_line(x + 8, y - 11, x + 12, y - 11, 1);
    video_line(x + 9, y - 12, x + 13, y - 12, 1);
    video_line(x + 10, y - 13, x + 14, y - 13, 1);
    video_line(x + 11, y - 14, x + 15, y - 14, 1);
    video_line(x + 12, y - 15, x + 16, y - 15, 1);
    video_line(x + 13, y - 16, x + 17, y - 16, 1);
    video_line(x + 14, y - 17, x + 18, y - 17, 1);
    video_line(x + 15, y - 18, x + 19, y - 18, 1);
    video_line(x + 16, y - 19, x + 20, y - 19, 1);
    video_line(x + 17, y - 20, x + 21, y - 20, 1);
    video_line(x + 18, y - 21, x + 22, y - 21, 1);
    video_line(x + 19, y - 22, x + 23, y - 22, 1);
    video_line(x + 20, y - 23, x + 24, y - 23, 1);
    // sides
    video_fill(x + 21, y - 24, x + 23, y - 27, 1);
    video_fill(x, y - 24, x + 2, y - 26, 1);
    // top
    video_line(x + 20, y - 28, x + 23, y - 28, 1);
    video_line(x + 19, y - 29, x + 22, y - 29, 1);
    video_line(x + 18, y - 30, x + 21, y - 30, 1);
    video_line(x + 17, y - 31, x + 20, y - 31, 1);
    video_line(x + 16, y - 32, x + 19, y - 32, 1);
    video_line(x, y - 27, x + 3, y - 27, 1);
    video_line(x + 1, y - 28, x + 4, y - 28, 1);
    video_line(x + 2, y - 29, x + 5, y - 29, 1);
    video_line(x + 3, y - 30, x + 6, y - 30, 1);
    video_line(x + 4, y - 31, x + 7, y - 31, 1);
    video_line(x + 5, y - 32, x + 8, y - 32, 1);
    video_line(x + 4, y - 33, x + 18, y - 33, 1);
    video_line(x + 5, y - 34, x + 17, y - 34, 1);
    video_line(x + 6, y - 35, x + 16, y - 34, 1);
}
void video_three(int x, int y) {
    // top sides
    video_fill(x + 21, y + 24, x + 23, y + 27,1);
    video_fill(x, y + 24, x + 2, y + 26,1);
    // top
    video_line(x + 20, y + 28, x + 23, y + 28,1);
    video_line(x + 19, y + 29, x + 22, y + 29,1);
    video_line(x + 18, y + 30, x + 21, y + 30,1);
    video_line(x + 17, y + 31, x + 20, y + 31,1);
    video_line(x + 16, y + 32, x + 19, y + 32,1);
    video_line(x, y + 27, x + 3, y + 27,1);
    video_line(x + 1, y + 28, x + 4, y + 28,1);
    video_line(x + 2, y + 29, x + 5, y + 29,1);
    video_line(x + 3, y + 30, x + 6, y + 30,1);
    video_line(x + 4, y + 31, x + 7, y + 31,1);
    video_line(x + 5, y + 32, x + 8, y + 32,1);
    video_line(x + 4, y + 33, x + 18, y + 33,1);
    video_line(x + 5, y + 34, x + 17, y + 34,1);
    video_line(x + 6, y + 35, x + 16, y + 34,1);
    
    // bottom sides
    video_fill(x, y + 7, x + 2, y + 11,1);
    video_fill(x + 21, y + 8, x + 23, y + 11,1);
    // bottom
    video_line(x, y + 6, x + 3, y + 6,1);
    video_line(x + 1, y + 5, x + 4, y + 5,1);
    video_line(x + 2, y + 4, x + 5, y + 4,1);
    video_line(x + 3, y + 3, x + 6, y + 3,1);
    video_line(x + 20, y + 7, x + 23, y + 7,1);
    video_line(x + 19, y + 6, x + 22, y + 6,1);
    video_line(x + 18, y + 5, x + 21, y + 5,1);
    video_line(x + 17, y + 4, x + 20, y + 4,1);
    video_line(x + 16, y + 3, x + 19, y + 3,1);
    video_line(x+4, y+2, x+18, y+2, 1);
    video_line(x+5, y+1, x+17, y+1,1);
    video_line(x+6,y,x+16,y,1);
    // middle
    video_fill(x + 19, y + 12, x + 22, y + 13,1);
    video_fill(x + 17, y + 13, x + 20, y + 14,1);
    video_fill(x + 15, y + 15, x + 19, y + 16,1);
    video_fill(x + 12, y + 17, x + 17, y + 18,1);
    video_fill(x + 15, y + 19, x + 19, y + 20,1);
    video_fill(x + 17, y + 21, x + 20, y + 22,1);
    video_fill(x + 19, y + 22, x + 22, y + 23,1);
}

void video_obstacle(int x, int y, int c) {
    video_fill(x, y, x + 10, y + 10, c);
}

void video_grass(int x, int y) {
    video_pt(x, y, 1);
    video_pt(x + 1, y + 1, 1);
    video_pt(x + 1, y + 2, 1);
    video_pt(x + 2, y + 3, 1);
    video_pt(x + 3, y + 2, 1);
    video_pt(x + 3, y + 1, 1);
    video_pt(x + 4, y, 1);
}

void video_car(int x, int y, int erase) {
    //car wheels
    video_line(x - 8, y - 6, x - 8, y - 11, erase);
    video_line(x - 8, y + 3, x - 8, y + 8, erase);
    video_line(x - 9, y - 6, x - 9, y - 11, erase);
    video_line(x - 9, y + 3, x - 9, y + 8, erase);

    video_line(x + 8, y - 6, x + 8, y - 11, erase);
    video_line(x + 8, y + 3, x + 8, y + 8, erase);
    video_line(x + 9, y - 6, x + 9, y - 11, erase);
    video_line(x + 9, y + 3, x + 9, y + 8, erase);


    //center lines
    video_line(x - 7, y - 12, x - 7, y + 8, erase);
    video_line(x + 7, y - 12, x + 7, y + 8, erase);
    video_line(x - 6, y - 13, x - 6, y + 9, erase);
    video_line(x + 6, y - 13, x + 6, y + 9, erase);

    video_line(x - 5, y - 14, x - 5, y + 10, erase);
    video_line(x + 5, y - 14, x + 5, y + 10, erase);

    video_line(x - 4, y - 15, x - 4, y + 11, erase);
    video_line(x + 4, y - 15, x + 4, y + 11, erase);

    video_line(x + 3, y - 15, x + 3, y + 11, erase);
    video_line(x - 3, y - 15, x - 3, y + 11, erase);
    video_line(x + 2, y - 15, x + 2, y + 11, erase);
    video_line(x - 2, y - 15, x - 2, y + 11, erase);
    video_line(x + 1, y - 15, x + 1, y + 11, erase);
    video_line(x - 1, y - 15, x - 1, y + 11, erase);
    video_line(x, y - 15, x, y + 11, erase);

    //middle black parts
    video_line(x + 5, y - 1, x - 5, y - 1, 0);
    video_line(x + 5, y - 2, x - 5, y - 2, 0);
    video_line(x + 5, y - 3, x - 5, y - 3, 0);
    video_line(x + 5, y - 4, x - 5, y - 4, 0);
    video_line(x + 4, y - 5, x - 4, y - 5, 0);
    video_line(x + 3, y - 6, x - 3, y - 6, 0);

    video_line(x + 5, y + 2, x - 5, y + 2, 0);
    video_line(x + 5, y + 3, x - 5, y + 3, 0);
    video_line(x + 5, y + 4, x - 5, y + 4, 0);
    video_line(x + 5, y + 5, x - 5, y + 5, 0);
    video_line(x + 4, y + 6, x - 4, y + 6, 0);
    video_line(x + 3, y + 7, x - 3, y + 7, 0);


}

void video_fill(int x1, int y1, int x2, int y2, char c) {
    static int i;
    for (i = y1; i < y2; i++) {
        video_line(x1, i, x2, i, c);
    }
}

void video_clear() {
    video_fill(0, 0, 256, 200, 0);
}
//==============================================================
//return the value of one point
//at x,y with color 1=white 0=black 2=invert

char video_state(int x, int y) {
    //The following construction
    //detects exactly one bit at the x,y location
    // int i = (x>>3) + ((int)y<<4) + ((int)y<<3);
    int i = (x >> 5) + y * word_per_line;
    return (screen_buffer[i] & pos[x & 0x1f]) != 0;
}

//===============================================================
// put a big character on the screen
// c is index into bitmap

void video_putchar(int x, int y, int c) {
    int i;
    int y_pos;
    int j;

    for (i = 0; i < 7; i++) {
        y_pos = y + i;

        j = ascii[c][i];

        video_pt_m(x, y_pos, (j & 0x80) == 0x80);
        video_pt_m(x + 1, y_pos, (j & 0x40) == 0x40);
        video_pt_m(x + 2, y_pos, (j & 0x20) == 0x20);
        video_pt_m(x + 3, y_pos, (j & 0x10) == 0x10);
        video_pt_m(x + 4, y_pos, (j & 0x08) == 0x08);
    }
}

//=============================================================
// put a string of big characters on the screen

void video_string(int x, int y, char *str) {
    char i;
    for (i = 0; str[i] != 0; i++) {
        video_putchar(x, y, str[i]);
        x = x + 6;
    }
}

//============================================================
// put a thick character on the screen
// c is index into bitmap

void video_big_putchar(int x, int y, int c) {
    int i;
    int y_pos;
    int j;

    for (i = 0; i < 7; i = i + 1) {
        y_pos = y + i;

        j = ascii[c][i];

        video_pt_m(x, y_pos, (j & 0x80) == 0x80);
        video_pt_m(x + 1, y_pos, (j & 0x80) == 0x80);
        video_pt_m(x + 2, y_pos, (j & 0x40) == 0x40);
        video_pt_m(x + 3, y_pos, (j & 0x40) == 0x40);
        video_pt_m(x + 4, y_pos, (j & 0x20) == 0x20);
        video_pt_m(x + 5, y_pos, (j & 0x40) == 0x40);
        video_pt_m(x + 6, y_pos, (j & 0x10) == 0x10);
        video_pt_m(x + 7, y_pos, (j & 0x10) == 0x10);
        video_pt_m(x + 8, y_pos, (j & 0x08) == 0x08);
        video_pt_m(x + 9, y_pos, (j & 0x08) == 0x08);
    }
}

//==================================================================
// put a string of thick characters on the screen

void video_bold_string(int x, int y, char *str) {
    char i;
    for (i = 0; str[i] != 0; i++) {
        video_big_putchar(x, y, str[i]);
        x = x + 10;
    }
}


void delay(int milliseconds)
{
    long pause;
    clock_t now,then;

    pause = milliseconds*(CLOCKS_PER_SEC/1000);
    now = then = clock();
    while( (now-then) < pause )
        now = clock();
}
// ========================================================================

int main(void) {
    // particle animation variables
#define nSamp 256
    int sample_number = 0; // index for balls and for next launch
    int flag = 0;
    int i = 0;
    int v_in[nSamp], v_disp[nSamp];
    fix v_fix[nSamp];

    // global time
    int time;
    // some strings
    char cu1[] = "Cornell  ECE 4760 -- PIC32 Racing Game";
    char time_string[10];


    char rules1[] = "The goal of the game is to reach a certain";
    char rules2[] = "distance in the shortest amount of time.";
    char rules3[] = "Use the steering wheel to avoid obstacles.";
    char rules4[] = "A collision results in a five second time";
    char rules5[] = "penalty, and the car will momentarily be";
    char rules6[] = "prevented from moving.";
    char rules7[] = "Press the start button to play. The";
    char rules8[] = "game will begin after 3 seconds.";

    // Configure the device for maximum performance but do not change the PBDIV
    // Given the options, this function will change the flash wait states, RAM
    // wait state and enable prefetch cache but will not change the PBDIV.
    // The PBDIV value is already set via the pragma FPBDIV option above..
    SYSTEMConfig(SYS_FREQ, SYS_CFG_WAIT_STATES | SYS_CFG_PCACHE);

    //make sure analog is cleared
    //ANSELA =0;
    //ANSELB =0;


    // timer 2 setup for one video line ===========================================
    // Set up timer2 on,  interrupts, internal clock, prescalar 1, compare-value
    // This timer generates the time base for each horizontal video line
    OpenTimer2(T2_ON | T2_SOURCE_INT | T2_PS_1_1, line_cycles);
    // set up the timer interrupt with a priority of 2
    ConfigIntTimer2(T2_INT_ON | T2_INT_PRIOR_2);
    mT2ClearIntFlag(); // and clear the interrupt flag
    // zero the system time tick which is updated in the ISR
    time_tick_60_hz = 0;

    // timer 3 setup for adc trigger  ==============================================
    // Set up timer3 on,  no interrupts, internal clock, prescalar 1, compare-value
    // This timer generates the time base for each ADC sample
    OpenTimer3(T3_ON | T3_SOURCE_INT | T3_PS_1_1, 60); //60 is 500 kHz (works at 33 -- is 900 kHz)
    // set up the timer interrupt with a priority of 2
    //ConfigIntTimer3(T3_INT_ON | T3_INT_PRIOR_2);
    //mT3ClearIntFlag(); // and clear the interrupt flag

    // ADC setup ===================================================================
    // trigger on timer3 match
    CloseADC10(); // ensure the ADC is off before setting the configuration

    // define  setup parameters for OpenADC10
    // Turn module on | ouput in integer | trigger mode auto | enable autosample
    // ADC_CLK_AUTO -- Internal counter ends sampling and starts conversion (Auto convert)
    // ADC_CLK_TMR -- triggered off timer3 match
    // ADC_AUTO_SAMPLING_ON -- Sampling begins immediately after last conversion completes; SAMP bit is automatically set
    // ADC_AUTO_SAMPLING_OFF -- Sampling begins with AcquireADC10();
#define PARAM1  ADC_FORMAT_INTG16 | ADC_CLK_AUTO | ADC_AUTO_SAMPLING_ON //ADC_CLK_TMR ADC_CLK_AUTO

    // define setup parameters for OpenADC10
    // ADC ref external  | disable offset test | disable scan mode | do 1 sample | use single buf | alternate mode off
#define PARAM2  ADC_VREF_AVDD_AVSS | ADC_OFFSET_CAL_DISABLE | ADC_SCAN_ON | ADC_SAMPLES_PER_INT_3 | ADC_ALT_BUF_OFF | ADC_ALT_INPUT_OFF
    //
    // Define setup parameters for OpenADC10
    // use peripherial bus clock | set sample time | set ADC clock divider
    // ADC_CONV_CLK_Tcy2 means divide CLK_PB by 2 (max speed)
    // ADC_SAMPLE_TIME_5 seems to work with a source resistance < 1kohm
    // At PB clock 30 MHz, divide by two for ADC_CONV_CLK gives 66 nSec
#define PARAM3 ADC_CONV_CLK_PB | ADC_SAMPLE_TIME_15 | ADC_CONV_CLK_Tcy //ADC_SAMPLE_TIME_15| ADC_CONV_CLK_Tcy2

    // define setup parameters for OpenADC10
    // set AN0 and  as analog inputs
#define PARAM4	ENABLE_AN0_ANA | ENABLE_AN4_ANA | ENABLE_AN5_ANA

    // define setup parameters for OpenADC10
    // do not assign channels to scan
#define PARAM5	SKIP_SCAN_AN1 | SKIP_SCAN_AN2 | SKIP_SCAN_AN3 | SKIP_SCAN_AN6 | SKIP_SCAN_AN7 | SKIP_SCAN_AN8 | SKIP_SCAN_AN9 | SKIP_SCAN_AN10 | SKIP_SCAN_AN11 | SKIP_SCAN_AN12 | SKIP_SCAN_AN13 | SKIP_SCAN_AN14 | SKIP_SCAN_AN15

    // use ground as neg ref for A | use AN0 for input A
    // configure to sample AN4
    SetChanADC10(ADC_CH0_NEG_SAMPLEA_NVREF); // configure to sample AN0
    OpenADC10(PARAM1, PARAM2, PARAM3, PARAM4, PARAM5); // configure ADC using the parameters defined above

    EnableADC10(); // Enable the ADC

    //=== DMA Channel 0 transfer ADC data to array v_in ================================
    // Open DMA Chan1 for later use sending video to TV
#define DMAchan0 0
    DmaChnOpen(DMAchan0, DMApri0, DMA_OPEN_DEFAULT);
    DmaChnSetTxfer(DMAchan0, (void*) &ADC1BUF0, (void*) v_in, 4, 1024, 4); //256 32-bit integers
    DmaChnSetEventControl(DMAchan0, DMA_EV_START_IRQ(28)); // 28 is ADC done


    // Compuare match setup for SYNC ===============================================
    //Set up compare match unit to produce sync pulses
    // 5 uSec low
    // or 63.5-5 = 58.5 microSec (2340 ticks) low
    // pulse duration will be controlled in Timer2 ISR
    // #define OpenOC2( config, value1, value2) ( OC2RS = (value1), OC2R = (value2), OC2CON = (config) )
    OpenOC2(OC_ON | OC_TIMER2_SRC | OC_CONTINUE_PULSE, line_cycles - 1, us_5_cycles);
    // OC2 is PPS group 2, map to RPB5 (pin 14)
    PPSOutput(2, RPB5, OC2);

    // Compare match OC3 setup for video delay =====================================
    // Compare unit for video timing, to delay DMA until end of backporch
    // using the interrupt flag to trigger the first DMA,
    // then use the ISR to change the DMA control to SPI
    // #define OpenOC2( config, value1, value2) ( OC2RS = (value1), OC2R = (value2), OC2CON = (config) )
    // Pulse needs to be TWO cycles long
    OpenOC3(OC_ON | OC_TIMER2_SRC | OC_CONTINUE_PULSE, us_10_cycles + 2, us_10_cycles); //
    // turn on ISR so that DMA can covert to SPI control
    ConfigIntOC3(OC_INT_PRIOR_1 | OC_INT_ON); //3 //  
    mOC3ClearIntFlag(); // and clear the interrupt flag

    // SPI configure ==============================================================
    // SCK1 is pin 25 RB14 -- not used here
    // SDO1 is PPS group 2, map to RPA1 (pin 3)
    // SDI1 is PPS group 2, map to RPB8 (pin 17) -- not used here
    // SS1 input is PPS group 1, map to RPB7 (pin 16) for framing -- not used here
    // specify PPS group, signal, logical pin name
    // PPSInput (1, SS1, RPB7);
    PPSOutput(2, RPA1, SDO1);
    // set up i/o
    mPORTBSetPinsDigitalOut(BIT_0 | BIT_1 | BIT_5);
    mPORTBSetBits(BIT_0);

    // divide Fpb by spiClkDiv, configure the I/O ports.
    // 32 bit transfer
    SpiChnOpen(spiChn, SPI_OPEN_ON | SPI_OPEN_MODE32 | SPI_OPEN_MSTEN, spiClkDiv);
    
    
    // Configure ISR for DAC ===================================================
     OpenTimer4(T4_ON | T4_SOURCE_INT | T4_PS_1_1, 909);
     ConfigIntTimer4(T4_INT_ON | T4_INT_PRIOR_2);
    mT4ClearIntFlag(); // and clear the interrupt flag
    // SPI2 configure ==========================================================

    PPSOutput(2, RPB11, SDO2);
    mPORTBSetPinsDigitalOut(BIT_13);
    mPORTBSetBits(BIT_13);
    SpiChnOpen(SPI_CHANNEL2, SPI_OPEN_ON | SPI_OPEN_MODE16 | SPI_OPEN_MSTEN | SPI_OPEN_CKE_REV, 4);

    for (i = 0; i < sine_table_size; i++) {
        sine_table[i] = (_Accum) (sin((float) i * 6.283 / (float) sine_table_size));
    }
    if (attack_time < 1) attack_time = 1;
    if (decay_time < 1) decay_time = 1;
    if (sustain_time < 1) sustain_time = 1;
    // set up increments for calculating bow envelope
    attack_inc = max_amplitude / (_Accum) attack_time;
    decay_inc = max_amplitude / (_Accum) decay_time;
    // set up increments for calculating FM envelope
    FM_attack_inc = FM_max_amplitude / (_Accum) FM_attack_time;
    FM_decay_inc = FM_max_amplitude / (_Accum) FM_decay_time;
    //=== DMA Channel 1 for TV signal ==========================================
    // Open DMA Chan1 for later use sending video to TV
    DmaChnOpen(DMAchn1, DMApri0, DMA_OPEN_DEFAULT);

    // === turn it all on ====================================================
    // setup system wide interrupts  ///
    INTEnableSystemMultiVectoredInt();

    EnablePullDownB(BIT_4);
    mPORTBSetPinsDigitalIn(BIT_4);
    flag = 0;
    // wait until start button is pressed; while waiting, display rules
    while (flag == 0) {
        video_string(0, top + 2, cu1);
        video_string(0, top + 30, rules1);
        video_string(0, top + 40, rules2);
        video_string(0, top + 60, rules3);
        video_string(0, top + 70, rules4);
        video_string(0, top + 80, rules5);
        video_string(0, top + 90, rules6);
        video_string(0, top + 110, rules7);
        video_string(0, top + 120, rules8);
        flag = mPORTBReadBits(BIT_4);
        if (flag) {
            video_clear();
        }
    }

    video_clear();
    video_three(127,87);
    int x = 2;
    while (x < 32767){
        int y = 2;
    while (y < 500){
        y++;
    }
        x++;
    }
    video_clear();
    video_two(127,117);
     x = 2;
    while (x < 32767){
        int y = 2;
    while (y < 1000){
        y++;
    }
        x++;
    }
    delay(1000);
    video_clear();
    video_one(130,87);
    x = 2;
    while (x < 32767){
        int y = 2;
    while (y < 1000){
        y++;
    }
        x++;
    }
    video_clear();
    
    

    //=== now the application ===============================================
    // Draw the screen boundaries
    video_line(left, top + 10, right, top + 10, 1); // Title line
    video_line(left, top, right, top, 1); // top
    video_line(right, top, right, bottom, 1); // right
    video_line(right, bottom, left, bottom, 1); // bottom
    video_line(left, top, left, bottom, 1); // left

    // Draw a title
    //Print "CORNELL" message
    video_string(15, top + 2, cu1);

    PT_INIT(&pt_anim);

    PT_SCHEDULE(protothread_anim(&pt_anim));


} // main