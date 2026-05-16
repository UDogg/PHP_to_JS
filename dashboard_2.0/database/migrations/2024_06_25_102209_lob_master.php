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
        if(!Schema::hasTable('lob_master'))
        {
            Schema::create('lob_master', function (Blueprint $table) {
                $table->id();
                $table->string('lob_name')->comment('Line of Business Name');
                $table->string('lob')->comment('Line of Business Code');
                $table->enum('is_enabled', ['Y', 'N'])->default('N')->comment('Broker selection of lob ');
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
    }
};
