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
        if(!Schema::hasTable('key_utility_mapping'))
        {
            Schema::create('key_utility_mapping', function (Blueprint $table) {
                $table->id();
                $table->integer('mapping_id')->nullable()->comment("common name for columns to show in policy report page");
                $table->integer('key_id')->nullable()->comment("key name from key_utility master table as foreign key");
                $table->integer('lob')->nullable()->comment("line of bussiness from lob_master table");
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
        Schema::dropIfExists('key_utility_mapping');
    }
};
