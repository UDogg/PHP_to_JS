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
        if(!Schema::hasTable('key_utility'))
        {
            Schema::create('key_utility', function (Blueprint $table) {
                $table->id();
                $table->string('key',100)->nullable()->comment("common name for columns to show in policy report page");
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
        Schema::dropIfExists('key_utility');
    }
};
