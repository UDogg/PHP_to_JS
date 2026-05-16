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
        //
        if(!Schema::hasTable('stage_master'))
        {
            Schema::create('stage_master',function(Blueprint $table) {
                $table->id();
                $table->string('stage_name')->nullable();
                $table->string('sub_stage_name',1000)->nullable();
                $table->timestamps();
                $table->softDeletes();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropIfExists('stage_master');
    }
};
