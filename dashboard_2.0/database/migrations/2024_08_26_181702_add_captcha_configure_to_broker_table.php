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

                if(!Schema::hasColumn('broker', 'captacha_configure'))
                {
                    $table->enum('captacha_configure', ['On', 'Off'])->default('Off');
                }

        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('broker', function (Blueprint $table) {
            //
        });
    }
};
