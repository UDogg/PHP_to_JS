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
        if(!Schema::hasTable('sub_stage_master'))
        {
            Schema::create('sub_stage_master', function (Blueprint $table) {
                $table->id();
                $table->string('sub_stage_name')->comment('all the substage are getting synced from mongodb at a specific time every day');
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropIfExists('sub_stage_master');
    }
};
