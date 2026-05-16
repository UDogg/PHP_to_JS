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
        if(Schema::hasTable('users'))
        {
            if(!Schema::hasColumn('users', 'oemId'))
            {
                Schema::table('users', function (Blueprint $table) {
                    $table->integer('oemId')->nullable();
                    $table->integer('mispId')->nullable();
                    $table->integer('branchId')->nullable();
                });
            }
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropColumns('users',['oemId','mispId','branchId']);
    }
};
