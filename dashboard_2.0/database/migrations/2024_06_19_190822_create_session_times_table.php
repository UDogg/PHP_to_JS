<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if(!Schema::hasTable('session_times')) {

            Schema::create('session_times', function (Blueprint $table) {
                $table->id('session_id');
                $table->time('session_time');
                $table->string('session_content');
                $table->string('broker_name');
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('session_times');
    }
};
