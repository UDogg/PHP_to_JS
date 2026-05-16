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
        Schema::table('broker', function (Blueprint $table) {
            $table->integer('city')->nullable()->change();
            $table->integer('state')->nullable()->change();
            
        });
    }
    

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
    }
};
